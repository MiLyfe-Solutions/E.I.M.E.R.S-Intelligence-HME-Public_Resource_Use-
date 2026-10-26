import V185TrunkScan23Chunk0188

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1119137 : List Nat := [1, 2, 3, 4, 1, 2, 1, 2, 3, 2, 2]
def baseStart_1119137 : Nat := 118140960795 + 1119137 * 2 ^ 59
def prefixEnd_1119137 : Nat := 4983230072969 + 3 ^ 40 * 1119137 * 2
def baseEnd_1119137 : Nat := 574655199230893105040689

theorem tailTrace_1119137 : CollatzResearch.WordTrace tailWord_1119137 prefixEnd_1119137 574655199230893105040689 := by
  unfold tailWord_1119137
  simp only [CollatzResearch.WordTrace]
  refine ⟨40818279746565257227803665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27212186497710171485202443 40818279746565257227803665)
  ·
    refine ⟨30613709809923942920852749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40818279746565257227803665 30613709809923942920852749)
    ·
      refine ⟨11480141178721478595319781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30613709809923942920852749 11480141178721478595319781)
      ·
        refine ⟨2152526471010277236622459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11480141178721478595319781 2152526471010277236622459)
        ·
          refine ⟨3228789706515415854933689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2152526471010277236622459 3228789706515415854933689)
          ·
            refine ⟨2421592279886561891200267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3228789706515415854933689 2421592279886561891200267)
            ·
              refine ⟨3632388419829842836800401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2421592279886561891200267 3632388419829842836800401)
              ·
                refine ⟨2724291314872382127600301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3632388419829842836800401 2724291314872382127600301)
                ·
                  refine ⟨1021609243077143297850113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2724291314872382127600301 1021609243077143297850113)
                  ·
                    refine ⟨766206932307857473387585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1021609243077143297850113 766206932307857473387585)
                    ·
                      refine ⟨574655199230893105040689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 766206932307857473387585 574655199230893105040689)
                      ·
                        rfl

theorem cell23_1119137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_1119137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1119137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1119137 prefixEnd_1119137 := by exact prefixLift 1119137
  have htrace : WordTrace (prefixWord ++ tailWord_1119137) baseStart_1119137 baseEnd_1119137 := by
    simpa [prefixWord, tailWord_1119137, baseEnd_1119137] using wordTrace_append hprefix tailTrace_1119137
  have hstable : (prefixWord ++ tailWord_1119137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119137).length < 2 ^ (prefixWord ++ tailWord_1119137).sum := by decide
  have hdescent : baseEnd_1119137 < baseStart_1119137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119181 : List Nat := [1, 6, 3, 1, 2, 1, 1, 1, 1, 6]
def baseStart_1119181 : Nat := 118140960795 + 1119181 * 2 ^ 59
def prefixEnd_1119181 : Nat := 4983230072969 + 3 ^ 40 * 1119181 * 2
def baseEnd_1119181 : Nat := 191559264126563644296829

theorem tailTrace_1119181 : CollatzResearch.WordTrace tailWord_1119181 prefixEnd_1119181 191559264126563644296829 := by
  unfold tailWord_1119181
  simp only [CollatzResearch.WordTrace]
  refine ⟨40819884558405852742405397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27213256372270568494936931 40819884558405852742405397)
  ·
    refine ⟨1913432088675274347300253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 40819884558405852742405397 1913432088675274347300253)
    ·
      refine ⟨717537033253227880237595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1913432088675274347300253 717537033253227880237595)
      ·
        refine ⟨1076305549879841820356393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 717537033253227880237595 1076305549879841820356393)
        ·
          refine ⟨807229162409881365267295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1076305549879841820356393 807229162409881365267295)
          ·
            refine ⟨1210843743614822047900943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 807229162409881365267295 1210843743614822047900943)
            ·
              refine ⟨1816265615422233071851415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1210843743614822047900943 1816265615422233071851415)
              ·
                refine ⟨2724398423133349607777123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1816265615422233071851415 2724398423133349607777123)
                ·
                  refine ⟨4086597634700024411665685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2724398423133349607777123 4086597634700024411665685)
                  ·
                    refine ⟨191559264126563644296829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4086597634700024411665685 191559264126563644296829)
                    ·
                      rfl

theorem cell23_1119181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_1119181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1119181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1119181 prefixEnd_1119181 := by exact prefixLift 1119181
  have htrace : WordTrace (prefixWord ++ tailWord_1119181) baseStart_1119181 baseEnd_1119181 := by
    simpa [prefixWord, tailWord_1119181, baseEnd_1119181] using wordTrace_append hprefix tailTrace_1119181
  have hstable : (prefixWord ++ tailWord_1119181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119181).length < 2 ^ (prefixWord ++ tailWord_1119181).sum := by decide
  have hdescent : baseEnd_1119181 < baseStart_1119181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119197 : List Nat := [1, 4, 3, 1, 2, 1, 1, 4, 1, 3, 2]
def baseStart_1119197 : Nat := 118140960795 + 1119197 * 2 ^ 59
def prefixEnd_1119197 : Nat := 4983230072969 + 3 ^ 40 * 1119197 * 2
def baseEnd_1119197 : Nat := 574686008070162870290413

theorem tailTrace_1119197 : CollatzResearch.WordTrace tailWord_1119197 prefixEnd_1119197 574686008070162870290413 := by
  unfold tailWord_1119197
  simp only [CollatzResearch.WordTrace]
  refine ⟨40820468126347887474987845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27213645417565258316658563 40820468126347887474987845)
  ·
    refine ⟨7653837773690228901560221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40820468126347887474987845 7653837773690228901560221)
    ·
      refine ⟨2870189165133835838085083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7653837773690228901560221 2870189165133835838085083)
      ·
        refine ⟨4305283747700753757127625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2870189165133835838085083 4305283747700753757127625)
        ·
          refine ⟨3228962810775565317845719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4305283747700753757127625 3228962810775565317845719)
          ·
            refine ⟨4843444216163347976768579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3228962810775565317845719 4843444216163347976768579)
            ·
              refine ⟨7265166324245021965152869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4843444216163347976768579 7265166324245021965152869)
              ·
                refine ⟨1362218685795941618466163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7265166324245021965152869 1362218685795941618466163)
                ·
                  refine ⟨2043328028693912427699245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1362218685795941618466163 2043328028693912427699245)
                  ·
                    refine ⟨766248010760217160387217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2043328028693912427699245 766248010760217160387217)
                    ·
                      refine ⟨574686008070162870290413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 766248010760217160387217 574686008070162870290413)
                      ·
                        rfl

theorem cell23_1119197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 4, 1, 3, 2].length) (baseStart_1119197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1119197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1119197 prefixEnd_1119197 := by exact prefixLift 1119197
  have htrace : WordTrace (prefixWord ++ tailWord_1119197) baseStart_1119197 baseEnd_1119197 := by
    simpa [prefixWord, tailWord_1119197, baseEnd_1119197] using wordTrace_append hprefix tailTrace_1119197
  have hstable : (prefixWord ++ tailWord_1119197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119197).length < 2 ^ (prefixWord ++ tailWord_1119197).sum := by decide
  have hdescent : baseEnd_1119197 < baseStart_1119197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119233 : List Nat := [1, 2, 4, 1, 2, 2, 3, 1, 7]
def baseStart_1119233 : Nat := 118140960795 + 1119233 * 2 ^ 59
def prefixEnd_1119233 : Nat := 4983230072969 + 3 ^ 40 * 1119233 * 2
def baseEnd_1119233 : Nat := 63856054819302747715583

theorem tailTrace_1119233 : CollatzResearch.WordTrace tailWord_1119233 prefixEnd_1119233 63856054819302747715583 := by
  unfold tailWord_1119233
  simp only [CollatzResearch.WordTrace]
  refine ⟨40821781154217465623298353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27214520769478310415532235 40821781154217465623298353)
  ·
    refine ⟨30616335865663099217473765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40821781154217465623298353 30616335865663099217473765)
    ·
      refine ⟨5740562974811831103276331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30616335865663099217473765 5740562974811831103276331)
      ·
        refine ⟨8610844462217746654914497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5740562974811831103276331 8610844462217746654914497)
        ·
          refine ⟨6458133346663309991185873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8610844462217746654914497 6458133346663309991185873)
          ·
            refine ⟨4843600009997482493389405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6458133346663309991185873 4843600009997482493389405)
            ·
              refine ⟨1816350003749055935021027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4843600009997482493389405 1816350003749055935021027)
              ·
                refine ⟨2724525005623583902531541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1816350003749055935021027 2724525005623583902531541)
                ·
                  refine ⟨63856054819302747715583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2724525005623583902531541 63856054819302747715583)
                  ·
                    rfl

theorem cell23_1119233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 1, 7].length) (baseStart_1119233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1119233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1119233 prefixEnd_1119233 := by exact prefixLift 1119233
  have htrace : WordTrace (prefixWord ++ tailWord_1119233) baseStart_1119233 baseEnd_1119233 := by
    simpa [prefixWord, tailWord_1119233, baseEnd_1119233] using wordTrace_append hprefix tailTrace_1119233
  have hstable : (prefixWord ++ tailWord_1119233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119233).length < 2 ^ (prefixWord ++ tailWord_1119233).sum := by decide
  have hdescent : baseEnd_1119233 < baseStart_1119233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119244 : List Nat := [2, 2, 1, 2, 3, 2, 4, 1, 2, 2, 2]
def baseStart_1119244 : Nat := 118140960795 + 1119244 * 2 ^ 59
def prefixEnd_1119244 : Nat := 4983230072969 + 3 ^ 40 * 1119244 * 2
def baseEnd_1119244 : Nat := 574710141660924186402697

theorem tailTrace_1119244 : CollatzResearch.WordTrace tailWord_1119244 prefixEnd_1119244 574710141660924186402697 := by
  unfold tailWord_1119244
  simp only [CollatzResearch.WordTrace]
  refine ⟨20411091178588807250974393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27214788238118409667965857 20411091178588807250974393)
  ·
    refine ⟨15308318383941605438230795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20411091178588807250974393 15308318383941605438230795)
    ·
      refine ⟨22962477575912408157346193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15308318383941605438230795 22962477575912408157346193)
      ·
        refine ⟨17221858181934306118009645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22962477575912408157346193 17221858181934306118009645)
        ·
          refine ⟨6458196818225364794253617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17221858181934306118009645 6458196818225364794253617)
          ·
            refine ⟨4843647613669023595690213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6458196818225364794253617 4843647613669023595690213)
            ·
              refine ⟨908183927562941924191915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4843647613669023595690213 908183927562941924191915)
              ·
                refine ⟨1362275891344412886287873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 908183927562941924191915 1362275891344412886287873)
                ·
                  refine ⟨1021706918508309664715905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1362275891344412886287873 1021706918508309664715905)
                  ·
                    refine ⟨766280188881232248536929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1021706918508309664715905 766280188881232248536929)
                    ·
                      refine ⟨574710141660924186402697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 766280188881232248536929 574710141660924186402697)
                      ·
                        rfl

theorem cell23_1119244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 4, 1, 2, 2, 2].length) (baseStart_1119244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1119244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1119244 prefixEnd_1119244 := by exact prefixLift 1119244
  have htrace : WordTrace (prefixWord ++ tailWord_1119244) baseStart_1119244 baseEnd_1119244 := by
    simpa [prefixWord, tailWord_1119244, baseEnd_1119244] using wordTrace_append hprefix tailTrace_1119244
  have hstable : (prefixWord ++ tailWord_1119244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119244).length < 2 ^ (prefixWord ++ tailWord_1119244).sum := by decide
  have hdescent : baseEnd_1119244 < baseStart_1119244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119263 : List Nat := [1, 1, 2, 4, 1, 3, 1, 3, 2, 5]
def baseStart_1119263 : Nat := 118140960795 + 1119263 * 2 ^ 59
def prefixEnd_1119263 : Nat := 4983230072969 + 3 ^ 40 * 1119263 * 2
def baseEnd_1119263 : Nat := 191573299264453204021703

theorem tailTrace_1119263 : CollatzResearch.WordTrace tailWord_1119263 prefixEnd_1119263 191573299264453204021703 := by
  unfold tailWord_1119263
  simp only [CollatzResearch.WordTrace]
  refine ⟨40822875344108780746890443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27215250229405853831260295 40822875344108780746890443)
  ·
    refine ⟨61234313016163171120335665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40822875344108780746890443 61234313016163171120335665)
    ·
      refine ⟨45925734762122378340251749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61234313016163171120335665 45925734762122378340251749)
      ·
        refine ⟨8611075267897945938797203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45925734762122378340251749 8611075267897945938797203)
        ·
          refine ⟨12916612901846918908195805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8611075267897945938797203 12916612901846918908195805)
          ·
            refine ⟨4843729838192594590573427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12916612901846918908195805 4843729838192594590573427)
            ·
              refine ⟨7265594757288891885860141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4843729838192594590573427 7265594757288891885860141)
              ·
                refine ⟨2724598033983334457197553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7265594757288891885860141 2724598033983334457197553)
                ·
                  refine ⟨2043448525487500842898165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2724598033983334457197553 2043448525487500842898165)
                  ·
                    refine ⟨191573299264453204021703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2043448525487500842898165 191573299264453204021703)
                    ·
                      rfl

theorem cell23_1119263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 3, 2, 5].length) (baseStart_1119263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1119263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1119263 prefixEnd_1119263 := by exact prefixLift 1119263
  have htrace : WordTrace (prefixWord ++ tailWord_1119263) baseStart_1119263 baseEnd_1119263 := by
    simpa [prefixWord, tailWord_1119263, baseEnd_1119263] using wordTrace_append hprefix tailTrace_1119263
  have hstable : (prefixWord ++ tailWord_1119263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119263).length < 2 ^ (prefixWord ++ tailWord_1119263).sum := by decide
  have hdescent : baseEnd_1119263 < baseStart_1119263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119284 : List Nat := [2, 5, 1, 2, 1, 1, 4, 2, 5]
def baseStart_1119284 : Nat := 118140960795 + 1119284 * 2 ^ 59
def prefixEnd_1119284 : Nat := 4983230072969 + 3 ^ 40 * 1119284 * 2
def baseEnd_1119284 : Nat := 63858964543011558878057

theorem tailTrace_1119284 : CollatzResearch.WordTrace tailWord_1119284 prefixEnd_1119284 63858964543011558878057 := by
  unfold tailWord_1119284
  simp only [CollatzResearch.WordTrace]
  refine ⟨20411820638516350666702453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27215760851355134222269937 20411820638516350666702453)
  ·
    refine ⟨1913608184860907875003355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20411820638516350666702453 1913608184860907875003355)
    ·
      refine ⟨2870412277291361812505033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1913608184860907875003355 2870412277291361812505033)
      ·
        refine ⟨2152809207968521359378775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2870412277291361812505033 2152809207968521359378775)
        ·
          refine ⟨3229213811952782039068163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2152809207968521359378775 3229213811952782039068163)
          ·
            refine ⟨4843820717929173058602245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3229213811952782039068163 4843820717929173058602245)
            ·
              refine ⟨908216384611719948487921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4843820717929173058602245 908216384611719948487921)
              ·
                refine ⟨681162288458789961365941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 908216384611719948487921 681162288458789961365941)
                ·
                  refine ⟨63858964543011558878057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 681162288458789961365941 63858964543011558878057)
                  ·
                    rfl

theorem cell23_1119284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 4, 2, 5].length) (baseStart_1119284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1119284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1119284 prefixEnd_1119284 := by exact prefixLift 1119284
  have htrace : WordTrace (prefixWord ++ tailWord_1119284) baseStart_1119284 baseEnd_1119284 := by
    simpa [prefixWord, tailWord_1119284, baseEnd_1119284] using wordTrace_append hprefix tailTrace_1119284
  have hstable : (prefixWord ++ tailWord_1119284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119284).length < 2 ^ (prefixWord ++ tailWord_1119284).sum := by decide
  have hdescent : baseEnd_1119284 < baseStart_1119284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119310 : List Nat := [4, 1, 1, 1, 1, 3, 3, 2, 3, 4]
def baseStart_1119310 : Nat := 118140960795 + 1119310 * 2 ^ 59
def prefixEnd_1119310 : Nat := 4983230072969 + 3 ^ 40 * 1119310 * 2
def baseEnd_1119310 : Nat := 191581343794706976059131

theorem tailTrace_1119310 : CollatzResearch.WordTrace tailWord_1119310 prefixEnd_1119310 191581343794706976059131 := by
  unfold tailWord_1119310
  simp only [CollatzResearch.WordTrace]
  refine ⟨5103073696867313471731423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27216393049959005182567589 5103073696867313471731423)
  ·
    refine ⟨7654610545300970207597135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5103073696867313471731423 7654610545300970207597135)
    ·
      refine ⟨11481915817951455311395703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7654610545300970207597135 11481915817951455311395703)
      ·
        refine ⟨17222873726927182967093555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11481915817951455311395703 17222873726927182967093555)
        ·
          refine ⟨25834310590390774450640333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17222873726927182967093555 25834310590390774450640333)
          ·
            refine ⟨9687866471396540418990125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25834310590390774450640333 9687866471396540418990125)
            ·
              refine ⟨3632949926773702657121297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9687866471396540418990125 3632949926773702657121297)
              ·
                refine ⟨2724712445080276992840973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3632949926773702657121297 2724712445080276992840973)
                ·
                  refine ⟨1021767166905103872315365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2724712445080276992840973 1021767166905103872315365)
                  ·
                    refine ⟨191581343794706976059131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1021767166905103872315365 191581343794706976059131)
                    ·
                      rfl

theorem cell23_1119310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 2, 3, 4].length) (baseStart_1119310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1119310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1119310 prefixEnd_1119310 := by exact prefixLift 1119310
  have htrace : WordTrace (prefixWord ++ tailWord_1119310) baseStart_1119310 baseEnd_1119310 := by
    simpa [prefixWord, tailWord_1119310, baseEnd_1119310] using wordTrace_append hprefix tailTrace_1119310
  have hstable : (prefixWord ++ tailWord_1119310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119310).length < 2 ^ (prefixWord ++ tailWord_1119310).sum := by decide
  have hdescent : baseEnd_1119310 < baseStart_1119310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119327 : List Nat := [1, 1, 2, 3, 1, 1, 6, 3, 1, 4]
def baseStart_1119327 : Nat := 118140960795 + 1119327 * 2 ^ 59
def prefixEnd_1119327 : Nat := 4983230072969 + 3 ^ 40 * 1119327 * 2
def baseEnd_1119327 : Nat := 191584253518415787221605

theorem tailTrace_1119327 : CollatzResearch.WordTrace tailWord_1119327 prefixEnd_1119327 191584253518415787221605 := by
  unfold tailWord_1119327
  simp only [CollatzResearch.WordTrace]
  refine ⟨40825209615876919677220235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27216806410584613118146823 40825209615876919677220235)
  ·
    refine ⟨61237814423815379515830353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40825209615876919677220235 61237814423815379515830353)
    ·
      refine ⟨45928360817861534636872765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61237814423815379515830353 45928360817861534636872765)
      ·
        refine ⟨17223135306698075488827287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45928360817861534636872765 17223135306698075488827287)
        ·
          refine ⟨25834702960047113233240931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17223135306698075488827287 25834702960047113233240931)
          ·
            refine ⟨38752054440070669849861397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25834702960047113233240931 38752054440070669849861397)
            ·
              refine ⟨1816502551878312649212253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 38752054440070669849861397 1816502551878312649212253)
              ·
                refine ⟨681188456954367243454595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1816502551878312649212253 681188456954367243454595)
                ·
                  refine ⟨1021782685431550865181893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 681188456954367243454595 1021782685431550865181893)
                  ·
                    refine ⟨191584253518415787221605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1021782685431550865181893 191584253518415787221605)
                    ·
                      rfl

theorem cell23_1119327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 3, 1, 4].length) (baseStart_1119327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1119327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1119327 prefixEnd_1119327 := by exact prefixLift 1119327
  have htrace : WordTrace (prefixWord ++ tailWord_1119327) baseStart_1119327 baseEnd_1119327 := by
    simpa [prefixWord, tailWord_1119327, baseEnd_1119327] using wordTrace_append hprefix tailTrace_1119327
  have hstable : (prefixWord ++ tailWord_1119327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119327).length < 2 ^ (prefixWord ++ tailWord_1119327).sum := by decide
  have hdescent : baseEnd_1119327 < baseStart_1119327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119330 : List Nat := [3, 3, 2, 2, 1, 1, 1, 1, 2, 1, 6]
def baseStart_1119330 : Nat := 118140960795 + 1119330 * 2 ^ 59
def prefixEnd_1119330 : Nat := 4983230072969 + 3 ^ 40 * 1119330 * 2
def baseEnd_1119330 : Nat := 574754300997210849927301

theorem tailTrace_1119330 : CollatzResearch.WordTrace tailWord_1119330 prefixEnd_1119330 574754300997210849927301 := by
  unfold tailWord_1119330
  simp only [CollatzResearch.WordTrace]
  refine ⟨10206329758716512797394861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27216879356577367459719629 10206329758716512797394861)
  ·
    refine ⟨3827373659518692299023073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10206329758716512797394861 3827373659518692299023073)
    ·
      refine ⟨2870530244639019224267305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3827373659518692299023073 2870530244639019224267305)
      ·
        refine ⟨2152897683479264418200479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2870530244639019224267305 2152897683479264418200479)
        ·
          refine ⟨3229346525218896627300719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2152897683479264418200479 3229346525218896627300719)
          ·
            refine ⟨4844019787828344940951079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3229346525218896627300719 4844019787828344940951079)
            ·
              refine ⟨7266029681742517411426619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4844019787828344940951079 7266029681742517411426619)
              ·
                refine ⟨10899044522613776117139929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7266029681742517411426619 10899044522613776117139929)
                ·
                  refine ⟨8174283391960332087854947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10899044522613776117139929 8174283391960332087854947)
                  ·
                    refine ⟨12261425087940498131782421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8174283391960332087854947 12261425087940498131782421)
                    ·
                      refine ⟨574754300997210849927301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12261425087940498131782421 574754300997210849927301)
                      ·
                        rfl

theorem cell23_1119330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_1119330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1119330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1119330 prefixEnd_1119330 := by exact prefixLift 1119330
  have htrace : WordTrace (prefixWord ++ tailWord_1119330) baseStart_1119330 baseEnd_1119330 := by
    simpa [prefixWord, tailWord_1119330, baseEnd_1119330] using wordTrace_append hprefix tailTrace_1119330
  have hstable : (prefixWord ++ tailWord_1119330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119330).length < 2 ^ (prefixWord ++ tailWord_1119330).sum := by decide
  have hdescent : baseEnd_1119330 < baseStart_1119330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119360 : List Nat := [2, 1, 1, 2, 1, 3, 3, 2, 1, 5, 2]
def baseStart_1119360 : Nat := 118140960795 + 1119360 * 2 ^ 59
def prefixEnd_1119360 : Nat := 4983230072969 + 3 ^ 40 * 1119360 * 2
def baseEnd_1119360 : Nat := 574769705416845732552163

theorem tailTrace_1119360 : CollatzResearch.WordTrace tailWord_1119360 prefixEnd_1119360 574769705416845732552163 := by
  unfold tailWord_1119360
  simp only [CollatzResearch.WordTrace]
  refine ⟨20413206612378683156585767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27217608816504910875447689 20413206612378683156585767)
  ·
    refine ⟨30619809918568024734878651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20413206612378683156585767 30619809918568024734878651)
    ·
      refine ⟨45929714877852037102317977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30619809918568024734878651 45929714877852037102317977)
      ·
        refine ⟨34447286158389027826738483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45929714877852037102317977 34447286158389027826738483)
        ·
          refine ⟨51670929237583541740107725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34447286158389027826738483 51670929237583541740107725)
          ·
            refine ⟨19376598464093828152540397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51670929237583541740107725 19376598464093828152540397)
            ·
              refine ⟨7266224424035185557202649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19376598464093828152540397 7266224424035185557202649)
              ·
                refine ⟨5449668318026389167901987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7266224424035185557202649 5449668318026389167901987)
                ·
                  refine ⟨8174502477039583751852981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5449668318026389167901987 8174502477039583751852981)
                  ·
                    refine ⟨766359607222460976736217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8174502477039583751852981 766359607222460976736217)
                    ·
                      refine ⟨574769705416845732552163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 766359607222460976736217 574769705416845732552163)
                      ·
                        rfl

theorem cell23_1119360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 1, 5, 2].length) (baseStart_1119360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1119360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1119360 prefixEnd_1119360 := by exact prefixLift 1119360
  have htrace : WordTrace (prefixWord ++ tailWord_1119360) baseStart_1119360 baseEnd_1119360 := by
    simpa [prefixWord, tailWord_1119360, baseEnd_1119360] using wordTrace_append hprefix tailTrace_1119360
  have hstable : (prefixWord ++ tailWord_1119360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119360).length < 2 ^ (prefixWord ++ tailWord_1119360).sum := by decide
  have hdescent : baseEnd_1119360 < baseStart_1119360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119410 : List Nat := [3, 2, 1, 1, 1, 4, 2, 2, 1, 1, 5]
def baseStart_1119410 : Nat := 118140960795 + 1119410 * 2 ^ 59
def prefixEnd_1119410 : Nat := 4983230072969 + 3 ^ 40 * 1119410 * 2
def baseEnd_1119410 : Nat := 574795379449570536926933

theorem tailTrace_1119410 : CollatzResearch.WordTrace tailWord_1119410 prefixEnd_1119410 574795379449570536926933 := by
  unfold tailWord_1119410
  simp only [CollatzResearch.WordTrace]
  refine ⟨10207059218644056213122921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27218824583050816568327789 10207059218644056213122921)
  ·
    refine ⟨7655294413983042159842191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10207059218644056213122921 7655294413983042159842191)
    ·
      refine ⟨11482941620974563239763287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7655294413983042159842191 11482941620974563239763287)
      ·
        refine ⟨17224412431461844859644931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11482941620974563239763287 17224412431461844859644931)
        ·
          refine ⟨25836618647192767289467397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17224412431461844859644931 25836618647192767289467397)
          ·
            refine ⟨4844365996348643866775137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25836618647192767289467397 4844365996348643866775137)
            ·
              refine ⟨3633274497261482900081353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4844365996348643866775137 3633274497261482900081353)
              ·
                refine ⟨2724955872946112175061015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3633274497261482900081353 2724955872946112175061015)
                ·
                  refine ⟨4087433809419168262591523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2724955872946112175061015 4087433809419168262591523)
                  ·
                    refine ⟨6131150714128752393887285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4087433809419168262591523 6131150714128752393887285)
                    ·
                      refine ⟨574795379449570536926933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6131150714128752393887285 574795379449570536926933)
                      ·
                        rfl

theorem cell23_1119410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 2, 1, 1, 5].length) (baseStart_1119410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1119410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1119410 prefixEnd_1119410 := by exact prefixLift 1119410
  have htrace : WordTrace (prefixWord ++ tailWord_1119410) baseStart_1119410 baseEnd_1119410 := by
    simpa [prefixWord, tailWord_1119410, baseEnd_1119410] using wordTrace_append hprefix tailTrace_1119410
  have hstable : (prefixWord ++ tailWord_1119410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119410).length < 2 ^ (prefixWord ++ tailWord_1119410).sum := by decide
  have hdescent : baseEnd_1119410 < baseStart_1119410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119417 : List Nat := [1, 2, 1, 4, 1, 4, 1, 3, 2, 4]
def baseStart_1119417 : Nat := 118140960795 + 1119417 * 2 ^ 59
def prefixEnd_1119417 : Nat := 4983230072969 + 3 ^ 40 * 1119417 * 2
def baseEnd_1119417 : Nat := 191599657938050669846467

theorem tailTrace_1119417 : CollatzResearch.WordTrace tailWord_1119417 prefixEnd_1119417 191599657938050669846467 := by
  unfold tailWord_1119417
  simp only [CollatzResearch.WordTrace]
  refine ⟨40828492185550865047996505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27218994790367243365331003 40828492185550865047996505)
  ·
    refine ⟨30621369139163148785997379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40828492185550865047996505 30621369139163148785997379)
    ·
      refine ⟨45932053708744723178996069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30621369139163148785997379 45932053708744723178996069)
      ·
        refine ⟨8612260070389635596061763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45932053708744723178996069 8612260070389635596061763)
        ·
          refine ⟨12918390105584453394092645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8612260070389635596061763 12918390105584453394092645)
          ·
            refine ⟨2422198144797085011392371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12918390105584453394092645 2422198144797085011392371)
            ·
              refine ⟨3633297217195627517088557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2422198144797085011392371 3633297217195627517088557)
              ·
                refine ⟨1362486456448360318908209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3633297217195627517088557 1362486456448360318908209)
                ·
                  refine ⟨1021864842336270239181157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1362486456448360318908209 1021864842336270239181157)
                  ·
                    refine ⟨191599657938050669846467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1021864842336270239181157 191599657938050669846467)
                    ·
                      rfl

theorem cell23_1119417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 3, 2, 4].length) (baseStart_1119417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1119417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1119417 prefixEnd_1119417 := by exact prefixLift 1119417
  have htrace : WordTrace (prefixWord ++ tailWord_1119417) baseStart_1119417 baseEnd_1119417 := by
    simpa [prefixWord, tailWord_1119417, baseEnd_1119417] using wordTrace_append hprefix tailTrace_1119417
  have hstable : (prefixWord ++ tailWord_1119417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119417).length < 2 ^ (prefixWord ++ tailWord_1119417).sum := by decide
  have hdescent : baseEnd_1119417 < baseStart_1119417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119420 : List Nat := [2, 2, 2, 3, 2, 1, 2, 1, 1, 1, 6]
def baseStart_1119420 : Nat := 118140960795 + 1119420 * 2 ^ 59
def prefixEnd_1119420 : Nat := 4983230072969 + 3 ^ 40 * 1119420 * 2
def baseEnd_1119420 : Nat := 574800514256115497801887

theorem tailTrace_1119420 : CollatzResearch.WordTrace tailWord_1119420 prefixEnd_1119420 574800514256115497801887 := by
  unfold tailWord_1119420
  simp only [CollatzResearch.WordTrace]
  refine ⟨20414300802269998280177857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27219067736359997706903809 20414300802269998280177857)
  ·
    refine ⟨15310725601702498710133393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20414300802269998280177857 15310725601702498710133393)
    ·
      refine ⟨11483044201276874032600045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15310725601702498710133393 11483044201276874032600045)
      ·
        refine ⟨4306141575478827762225017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11483044201276874032600045 4306141575478827762225017)
        ·
          refine ⟨3229606181609120821668763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4306141575478827762225017 3229606181609120821668763)
          ·
            refine ⟨4844409272413681232503145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3229606181609120821668763 4844409272413681232503145)
            ·
              refine ⟨3633306954310260924377359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4844409272413681232503145 3633306954310260924377359)
              ·
                refine ⟨5449960431465391386566039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3633306954310260924377359 5449960431465391386566039)
                ·
                  refine ⟨8174940647198087079849059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5449960431465391386566039 8174940647198087079849059)
                  ·
                    refine ⟨12262410970797130619773589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8174940647198087079849059 12262410970797130619773589)
                    ·
                      refine ⟨574800514256115497801887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12262410970797130619773589 574800514256115497801887)
                      ·
                        rfl

theorem cell23_1119420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_1119420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1119420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1119420 prefixEnd_1119420 := by exact prefixLift 1119420
  have htrace : WordTrace (prefixWord ++ tailWord_1119420) baseStart_1119420 baseEnd_1119420 := by
    simpa [prefixWord, tailWord_1119420, baseEnd_1119420] using wordTrace_append hprefix tailTrace_1119420
  have hstable : (prefixWord ++ tailWord_1119420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119420).length < 2 ^ (prefixWord ++ tailWord_1119420).sum := by decide
  have hdescent : baseEnd_1119420 < baseStart_1119420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119424 : List Nat := [2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 4]
def baseStart_1119424 : Nat := 118140960795 + 1119424 * 2 ^ 59
def prefixEnd_1119424 : Nat := 4983230072969 + 3 ^ 40 * 1119424 * 2
def baseEnd_1119424 : Nat := 574802568178733482151869

theorem tailTrace_1119424 : CollatzResearch.WordTrace tailWord_1119424 prefixEnd_1119424 574802568178733482151869 := by
  unfold tailWord_1119424
  simp only [CollatzResearch.WordTrace]
  refine ⟨20414373748262752621750663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27219164997683670162334217 20414373748262752621750663)
  ·
    refine ⟨30621560622394128932625995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20414373748262752621750663 30621560622394128932625995)
    ·
      refine ⟨45932340933591193398938993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30621560622394128932625995 45932340933591193398938993)
      ·
        refine ⟨34449255700193395049204245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45932340933591193398938993 34449255700193395049204245)
        ·
          refine ⟨1614808860946565392931449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 34449255700193395049204245 1614808860946565392931449)
          ·
            refine ⟨1211106645709924044698587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1614808860946565392931449 1211106645709924044698587)
            ·
              refine ⟨1816659968564886067047881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1211106645709924044698587 1816659968564886067047881)
              ·
                refine ⟨1362494976423664550285911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1816659968564886067047881 1362494976423664550285911)
                ·
                  refine ⟨2043742464635496825428867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1362494976423664550285911 2043742464635496825428867)
                  ·
                    refine ⟨3065613696953245238143301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2043742464635496825428867 3065613696953245238143301)
                    ·
                      refine ⟨574802568178733482151869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3065613696953245238143301 574802568178733482151869)
                      ·
                        rfl

theorem cell23_1119424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 4].length) (baseStart_1119424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1119424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1119424 prefixEnd_1119424 := by exact prefixLift 1119424
  have htrace : WordTrace (prefixWord ++ tailWord_1119424) baseStart_1119424 baseEnd_1119424 := by
    simpa [prefixWord, tailWord_1119424, baseEnd_1119424] using wordTrace_append hprefix tailTrace_1119424
  have hstable : (prefixWord ++ tailWord_1119424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119424).length < 2 ^ (prefixWord ++ tailWord_1119424).sum := by decide
  have hdescent : baseEnd_1119424 < baseStart_1119424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119467 : List Nat := [1, 1, 1, 1, 2, 6, 1, 2, 3, 3, 2]
def baseStart_1119467 : Nat := 118140960795 + 1119467 * 2 ^ 59
def prefixEnd_1119467 : Nat := 4983230072969 + 3 ^ 40 * 1119467 * 2
def baseEnd_1119467 : Nat := 574824647846876813914171

theorem tailTrace_1119467 : CollatzResearch.WordTrace tailWord_1119467 prefixEnd_1119467 574824647846876813914171 := by
  unfold tailWord_1119467
  simp only [CollatzResearch.WordTrace]
  refine ⟨40830315835369723587316655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27220210556913149058211103 40830315835369723587316655)
  ·
    refine ⟨61245473753054585380974983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40830315835369723587316655 61245473753054585380974983)
    ·
      refine ⟨91868210629581878071462475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61245473753054585380974983 91868210629581878071462475)
      ·
        refine ⟨137802315944372817107193713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91868210629581878071462475 137802315944372817107193713)
        ·
          refine ⟨103351736958279612830395285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137802315944372817107193713 103351736958279612830395285)
          ·
            refine ⟨4844612669919356851424779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 103351736958279612830395285 4844612669919356851424779)
            ·
              refine ⟨7266919004879035277137169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4844612669919356851424779 7266919004879035277137169)
              ·
                refine ⟨5450189253659276457852877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7266919004879035277137169 5450189253659276457852877)
                ·
                  refine ⟨2043820970122228671694829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5450189253659276457852877 2043820970122228671694829)
                  ·
                    refine ⟨766432863795835751885561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2043820970122228671694829 766432863795835751885561)
                    ·
                      refine ⟨574824647846876813914171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 766432863795835751885561 574824647846876813914171)
                      ·
                        rfl

theorem cell23_1119467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 3, 3, 2].length) (baseStart_1119467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1119467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1119467 prefixEnd_1119467 := by exact prefixLift 1119467
  have htrace : WordTrace (prefixWord ++ tailWord_1119467) baseStart_1119467 baseEnd_1119467 := by
    simpa [prefixWord, tailWord_1119467, baseEnd_1119467] using wordTrace_append hprefix tailTrace_1119467
  have hstable : (prefixWord ++ tailWord_1119467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119467).length < 2 ^ (prefixWord ++ tailWord_1119467).sum := by decide
  have hdescent : baseEnd_1119467 < baseStart_1119467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119474 : List Nat := [3, 2, 1, 3, 3, 1, 2, 1, 1, 3, 3]
def baseStart_1119474 : Nat := 118140960795 + 1119474 * 2 ^ 59
def prefixEnd_1119474 : Nat := 4983230072969 + 3 ^ 40 * 1119474 * 2
def baseEnd_1119474 : Nat := 574828242211458286526639

theorem tailTrace_1119474 : CollatzResearch.WordTrace tailWord_1119474 prefixEnd_1119474 574828242211458286526639 := by
  unfold tailWord_1119474
  simp only [CollatzResearch.WordTrace]
  refine ⟨10207642786586090945705369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27220380764229575855214317 10207642786586090945705369)
  ·
    refine ⟨7655732089939568209279027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10207642786586090945705369 7655732089939568209279027)
    ·
      refine ⟨11483598134909352313918541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7655732089939568209279027 11483598134909352313918541)
      ·
        refine ⟨4306349300591007117719453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11483598134909352313918541 4306349300591007117719453)
        ·
          refine ⟨1614880987721627669144795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4306349300591007117719453 1614880987721627669144795)
          ·
            refine ⟨2422321481582441503717193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1614880987721627669144795 2422321481582441503717193)
            ·
              refine ⟨1816741111186831127787895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2422321481582441503717193 1816741111186831127787895)
              ·
                refine ⟨2725111666780246691681843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1816741111186831127787895 2725111666780246691681843)
                ·
                  refine ⟨4087667500170370037522765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2725111666780246691681843 4087667500170370037522765)
                  ·
                    refine ⟨1532875312563888764071037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4087667500170370037522765 1532875312563888764071037)
                    ·
                      refine ⟨574828242211458286526639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1532875312563888764071037 574828242211458286526639)
                      ·
                        rfl

theorem cell23_1119474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_1119474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1119474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1119474 prefixEnd_1119474 := by exact prefixLift 1119474
  have htrace : WordTrace (prefixWord ++ tailWord_1119474) baseStart_1119474 baseEnd_1119474 := by
    simpa [prefixWord, tailWord_1119474, baseEnd_1119474] using wordTrace_append hprefix tailTrace_1119474
  have hstable : (prefixWord ++ tailWord_1119474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119474).length < 2 ^ (prefixWord ++ tailWord_1119474).sum := by decide
  have hdescent : baseEnd_1119474 < baseStart_1119474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119497 : List Nat := [1, 2, 1, 1, 3, 3, 1, 4, 1, 4, 2]
def baseStart_1119497 : Nat := 118140960795 + 1119497 * 2 ^ 59
def prefixEnd_1119497 : Nat := 4983230072969 + 3 ^ 40 * 1119497 * 2
def baseEnd_1119497 : Nat := 574840052266511696539033

theorem tailTrace_1119497 : CollatzResearch.WordTrace tailWord_1119497 prefixEnd_1119497 574840052266511696539033 := by
  unfold tailWord_1119497
  simp only [CollatzResearch.WordTrace]
  refine ⟨40831410025261038710908745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27220940016840692473939163 40831410025261038710908745)
  ·
    refine ⟨30623557518945779033181559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40831410025261038710908745 30623557518945779033181559)
    ·
      refine ⟨45935336278418668549772339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30623557518945779033181559 45935336278418668549772339)
      ·
        refine ⟨68903004417628002824658509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45935336278418668549772339 68903004417628002824658509)
        ·
          refine ⟨25838626656610501059246941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68903004417628002824658509 25838626656610501059246941)
          ·
            refine ⟨9689484996228937897217603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25838626656610501059246941 9689484996228937897217603)
            ·
              refine ⟨14534227494343406845826405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9689484996228937897217603 14534227494343406845826405)
              ·
                refine ⟨2725167655189388783592451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14534227494343406845826405 2725167655189388783592451)
                ·
                  refine ⟨4087751482784083175388677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2725167655189388783592451 4087751482784083175388677)
                  ·
                    refine ⟨766453403022015595385377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4087751482784083175388677 766453403022015595385377)
                    ·
                      refine ⟨574840052266511696539033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 766453403022015595385377 574840052266511696539033)
                      ·
                        rfl

theorem cell23_1119497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 4, 1, 4, 2].length) (baseStart_1119497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1119497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1119497 prefixEnd_1119497 := by exact prefixLift 1119497
  have htrace : WordTrace (prefixWord ++ tailWord_1119497) baseStart_1119497 baseEnd_1119497 := by
    simpa [prefixWord, tailWord_1119497, baseEnd_1119497] using wordTrace_append hprefix tailTrace_1119497
  have hstable : (prefixWord ++ tailWord_1119497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119497).length < 2 ^ (prefixWord ++ tailWord_1119497).sum := by decide
  have hdescent : baseEnd_1119497 < baseStart_1119497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119560 : List Nat := [2, 1, 3, 1, 1, 2, 1, 4, 1, 2, 5]
def baseStart_1119560 : Nat := 118140960795 + 1119560 * 2 ^ 59
def prefixEnd_1119560 : Nat := 4983230072969 + 3 ^ 40 * 1119560 * 2
def baseEnd_1119560 : Nat := 574872401547744950051243

theorem tailTrace_1119560 : CollatzResearch.WordTrace tailWord_1119560 prefixEnd_1119560 574872401547744950051243 := by
  unfold tailWord_1119560
  simp only [CollatzResearch.WordTrace]
  refine ⟨20416853912016400235226067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27222471882688533646968089 20416853912016400235226067)
  ·
    refine ⟨30625280868024600352839101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20416853912016400235226067 30625280868024600352839101)
    ·
      refine ⟨11484480325509225132314663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30625280868024600352839101 11484480325509225132314663)
      ·
        refine ⟨17226720488263837698471995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11484480325509225132314663 17226720488263837698471995)
        ·
          refine ⟨25840080732395756547707993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17226720488263837698471995 25840080732395756547707993)
          ·
            refine ⟨19380060549296817410780995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25840080732395756547707993 19380060549296817410780995)
            ·
              refine ⟨29070090823945226116171493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19380060549296817410780995 29070090823945226116171493)
              ·
                refine ⟨5450642029489729896782155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29070090823945226116171493 5450642029489729896782155)
                ·
                  refine ⟨8175963044234594845173233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5450642029489729896782155 8175963044234594845173233)
                  ·
                    refine ⟨6131972283175946133879925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8175963044234594845173233 6131972283175946133879925)
                    ·
                      refine ⟨574872401547744950051243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6131972283175946133879925 574872401547744950051243)
                      ·
                        rfl

theorem cell23_1119560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 1, 2, 5].length) (baseStart_1119560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1119560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1119560 prefixEnd_1119560 := by exact prefixLift 1119560
  have htrace : WordTrace (prefixWord ++ tailWord_1119560) baseStart_1119560 baseEnd_1119560 := by
    simpa [prefixWord, tailWord_1119560, baseEnd_1119560] using wordTrace_append hprefix tailTrace_1119560
  have hstable : (prefixWord ++ tailWord_1119560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119560).length < 2 ^ (prefixWord ++ tailWord_1119560).sum := by decide
  have hdescent : baseEnd_1119560 < baseStart_1119560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119624 : List Nat := [2, 1, 3, 3, 1, 2, 2, 2, 2, 2, 3]
def baseStart_1119624 : Nat := 118140960795 + 1119624 * 2 ^ 59
def prefixEnd_1119624 : Nat := 4983230072969 + 3 ^ 40 * 1119624 * 2
def baseEnd_1119624 : Nat := 574905264309632699650949

theorem tailTrace_1119624 : CollatzResearch.WordTrace tailWord_1119624 prefixEnd_1119624 574905264309632699650949 := by
  unfold tailWord_1119624
  simp only [CollatzResearch.WordTrace]
  refine ⟨20418021047900469700390963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27224028063867292933854617 20418021047900469700390963)
  ·
    refine ⟨30627031571850704550586445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20418021047900469700390963 30627031571850704550586445)
    ·
      refine ⟨11485136839444014206469917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30627031571850704550586445 11485136839444014206469917)
      ·
        refine ⟨4306926314791505327426219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11485136839444014206469917 4306926314791505327426219)
        ·
          refine ⟨6460389472187257991139329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4306926314791505327426219 6460389472187257991139329)
          ·
            refine ⟨4845292104140443493354497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6460389472187257991139329 4845292104140443493354497)
            ·
              refine ⟨3633969078105332620015873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4845292104140443493354497 3633969078105332620015873)
              ·
                refine ⟨2725476808578999465011905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3633969078105332620015873 2725476808578999465011905)
                ·
                  refine ⟨2044107606434249598758929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2725476808578999465011905 2044107606434249598758929)
                  ·
                    refine ⟨1533080704825687199069197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2044107606434249598758929 1533080704825687199069197)
                    ·
                      refine ⟨574905264309632699650949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1533080704825687199069197 574905264309632699650949)
                      ·
                        rfl

theorem cell23_1119624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_1119624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1119624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1119624 prefixEnd_1119624 := by exact prefixLift 1119624
  have htrace : WordTrace (prefixWord ++ tailWord_1119624) baseStart_1119624 baseEnd_1119624 := by
    simpa [prefixWord, tailWord_1119624, baseEnd_1119624] using wordTrace_append hprefix tailTrace_1119624
  have hstable : (prefixWord ++ tailWord_1119624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119624).length < 2 ^ (prefixWord ++ tailWord_1119624).sum := by decide
  have hdescent : baseEnd_1119624 < baseStart_1119624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119627 : List Nat := [1, 1, 1, 1, 4, 3, 4, 2, 6]
def baseStart_1119627 : Nat := 118140960795 + 1119627 * 2 ^ 59
def prefixEnd_1119627 : Nat := 4983230072969 + 3 ^ 40 * 1119627 * 2
def baseEnd_1119627 : Nat := 63878533861288465323715

theorem tailTrace_1119627 : CollatzResearch.WordTrace tailWord_1119627 prefixEnd_1119627 63878533861288465323715 := by
  unfold tailWord_1119627
  simp only [CollatzResearch.WordTrace]
  refine ⟨40836151514790070913141135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27224101009860047275427423 40836151514790070913141135)
  ·
    refine ⟨61254227272185106369711703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40836151514790070913141135 61254227272185106369711703)
    ·
      refine ⟨91881340908277659554567555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61254227272185106369711703 91881340908277659554567555)
      ·
        refine ⟨137822011362416489331851333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91881340908277659554567555 137822011362416489331851333)
        ·
          refine ⟨25841627130453091749722125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 137822011362416489331851333 25841627130453091749722125)
          ·
            refine ⟨9690610173919909406145797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25841627130453091749722125 9690610173919909406145797)
            ·
              refine ⟨1816989407609983013652337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9690610173919909406145797 1816989407609983013652337)
              ·
                refine ⟨1362742055707487260239253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1816989407609983013652337 1362742055707487260239253)
                ·
                  refine ⟨63878533861288465323715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1362742055707487260239253 63878533861288465323715)
                  ·
                    rfl

theorem cell23_1119627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 2, 6].length) (baseStart_1119627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1119627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1119627 prefixEnd_1119627 := by exact prefixLift 1119627
  have htrace : WordTrace (prefixWord ++ tailWord_1119627) baseStart_1119627 baseEnd_1119627 := by
    simpa [prefixWord, tailWord_1119627, baseEnd_1119627] using wordTrace_append hprefix tailTrace_1119627
  have hstable : (prefixWord ++ tailWord_1119627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119627).length < 2 ^ (prefixWord ++ tailWord_1119627).sum := by decide
  have hdescent : baseEnd_1119627 < baseStart_1119627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119664 : List Nat := [2, 1, 1, 1, 2, 1, 1, 7, 2, 3, 2]
def baseStart_1119664 : Nat := 118140960795 + 1119664 * 2 ^ 59
def prefixEnd_1119664 : Nat := 4983230072969 + 3 ^ 40 * 1119664 * 2
def baseEnd_1119664 : Nat := 574925803535812543150765

theorem tailTrace_1119664 : CollatzResearch.WordTrace tailWord_1119664 prefixEnd_1119664 574925803535812543150765 := by
  unfold tailWord_1119664
  simp only [CollatzResearch.WordTrace]
  refine ⟨20418750507828013116119023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27225000677104017488158697 20418750507828013116119023)
  ·
    refine ⟨30628125761742019674178535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20418750507828013116119023 30628125761742019674178535)
    ·
      refine ⟨45942188642613029511267803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30628125761742019674178535 45942188642613029511267803)
      ·
        refine ⟨68913282963919544266901705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45942188642613029511267803 68913282963919544266901705)
        ·
          refine ⟨51684962222939658200176279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68913282963919544266901705 51684962222939658200176279)
          ·
            refine ⟨77527443334409487300264419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51684962222939658200176279 77527443334409487300264419)
            ·
              refine ⟨116291165001614230950396629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77527443334409487300264419 116291165001614230950396629)
              ·
                refine ⟨2725574179725333537899921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 116291165001614230950396629 2725574179725333537899921)
                ·
                  refine ⟨2044180634794000153424941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2725574179725333537899921 2044180634794000153424941)
                  ·
                    refine ⟨766567738047750057534353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2044180634794000153424941 766567738047750057534353)
                    ·
                      refine ⟨574925803535812543150765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 766567738047750057534353 574925803535812543150765)
                      ·
                        rfl

theorem cell23_1119664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 7, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 7, 2, 3, 2].length) (baseStart_1119664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1119664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1119664 prefixEnd_1119664 := by exact prefixLift 1119664
  have htrace : WordTrace (prefixWord ++ tailWord_1119664) baseStart_1119664 baseEnd_1119664 := by
    simpa [prefixWord, tailWord_1119664, baseEnd_1119664] using wordTrace_append hprefix tailTrace_1119664
  have hstable : (prefixWord ++ tailWord_1119664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119664).length < 2 ^ (prefixWord ++ tailWord_1119664).sum := by decide
  have hdescent : baseEnd_1119664 < baseStart_1119664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119682 : List Nat := [3, 5, 2, 1, 1, 1, 2, 1, 3, 4]
def baseStart_1119682 : Nat := 118140960795 + 1119682 * 2 ^ 59
def prefixEnd_1119682 : Nat := 4983230072969 + 3 ^ 40 * 1119682 * 2
def baseEnd_1119682 : Nat := 191645015395864490908561

theorem tailTrace_1119682 : CollatzResearch.WordTrace tailWord_1119682 prefixEnd_1119682 191645015395864490908561 := by
  unfold tailWord_1119682
  simp only [CollatzResearch.WordTrace]
  refine ⟨10209539382397703826598325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27225438353060543537595533 10209539382397703826598325)
  ·
    refine ⟨957144317099784733743593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10209539382397703826598325 957144317099784733743593)
    ·
      refine ⟨717858237824838550307695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 957144317099784733743593 717858237824838550307695)
      ·
        refine ⟨1076787356737257825461543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 717858237824838550307695 1076787356737257825461543)
        ·
          refine ⟨1615181035105886738192315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1076787356737257825461543 1615181035105886738192315)
          ·
            refine ⟨2422771552658830107288473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1615181035105886738192315 2422771552658830107288473)
            ·
              refine ⟨1817078664494122580466355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2422771552658830107288473 1817078664494122580466355)
              ·
                refine ⟨2725617996741183870699533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1817078664494122580466355 2725617996741183870699533)
                ·
                  refine ⟨1022106748777943951512325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2725617996741183870699533 1022106748777943951512325)
                  ·
                    refine ⟨191645015395864490908561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1022106748777943951512325 191645015395864490908561)
                    ·
                      rfl

theorem cell23_1119682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_1119682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1119682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1119682 prefixEnd_1119682 := by exact prefixLift 1119682
  have htrace : WordTrace (prefixWord ++ tailWord_1119682) baseStart_1119682 baseEnd_1119682 := by
    simpa [prefixWord, tailWord_1119682, baseEnd_1119682] using wordTrace_append hprefix tailTrace_1119682
  have hstable : (prefixWord ++ tailWord_1119682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119682).length < 2 ^ (prefixWord ++ tailWord_1119682).sum := by decide
  have hdescent : baseEnd_1119682 < baseStart_1119682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119704 : List Nat := [2, 1, 2, 2, 2, 1, 2, 5, 2, 4]
def baseStart_1119704 : Nat := 118140960795 + 1119704 * 2 ^ 59
def prefixEnd_1119704 : Nat := 4983230072969 + 3 ^ 40 * 1119704 * 2
def baseEnd_1119704 : Nat := 191648780920664128883527

theorem tailTrace_1119704 : CollatzResearch.WordTrace tailWord_1119704 prefixEnd_1119704 191648780920664128883527 := by
  unfold tailWord_1119704
  simp only [CollatzResearch.WordTrace]
  refine ⟨20419479967755556531847083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27225973290340742042462777 20419479967755556531847083)
  ·
    refine ⟨30629219951633334797770625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20419479967755556531847083 30629219951633334797770625)
    ·
      refine ⟨22971914963725001098327969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30629219951633334797770625 22971914963725001098327969)
      ·
        refine ⟨17228936222793750823745977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22971914963725001098327969 17228936222793750823745977)
        ·
          refine ⟨12921702167095313117809483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17228936222793750823745977 12921702167095313117809483)
          ·
            refine ⟨19382553250642969676714225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12921702167095313117809483 19382553250642969676714225)
            ·
              refine ⟨14536914937982227257535669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19382553250642969676714225 14536914937982227257535669)
              ·
                refine ⟨1362835775435833805393969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14536914937982227257535669 1362835775435833805393969)
                ·
                  refine ⟨1022126831576875354045477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1362835775435833805393969 1022126831576875354045477)
                  ·
                    refine ⟨191648780920664128883527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1022126831576875354045477 191648780920664128883527)
                    ·
                      rfl

theorem cell23_1119704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 5, 2, 4].length) (baseStart_1119704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1119704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1119704 prefixEnd_1119704 := by exact prefixLift 1119704
  have htrace : WordTrace (prefixWord ++ tailWord_1119704) baseStart_1119704 baseEnd_1119704 := by
    simpa [prefixWord, tailWord_1119704, baseEnd_1119704] using wordTrace_append hprefix tailTrace_1119704
  have hstable : (prefixWord ++ tailWord_1119704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119704).length < 2 ^ (prefixWord ++ tailWord_1119704).sum := by decide
  have hdescent : baseEnd_1119704 < baseStart_1119704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119711 : List Nat := [1, 1, 2, 3, 3, 1, 1, 4, 3, 2, 2]
def baseStart_1119711 : Nat := 118140960795 + 1119711 * 2 ^ 59
def prefixEnd_1119711 : Nat := 4983230072969 + 3 ^ 40 * 1119711 * 2
def baseEnd_1119711 : Nat := 574949937126573859263049

theorem tailTrace_1119711 : CollatzResearch.WordTrace tailWord_1119711 prefixEnd_1119711 574949937126573859263049 := by
  unfold tailWord_1119711
  simp only [CollatzResearch.WordTrace]
  refine ⟨40839215246485753259198987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27226143497657168839465991 40839215246485753259198987)
  ·
    refine ⟨61258822869728629888798481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40839215246485753259198987 61258822869728629888798481)
    ·
      refine ⟨45944117152296472416598861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61258822869728629888798481 45944117152296472416598861)
      ·
        refine ⟨17229043932111177156224573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45944117152296472416598861 17229043932111177156224573)
        ·
          refine ⟨6460891474541691433584215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17229043932111177156224573 6460891474541691433584215)
          ·
            refine ⟨9691337211812537150376323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6460891474541691433584215 9691337211812537150376323)
            ·
              refine ⟨14537005817718805725564485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9691337211812537150376323 14537005817718805725564485)
              ·
                refine ⟨2725688590822276073543341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14537005817718805725564485 2725688590822276073543341)
                ·
                  refine ⟨1022133221558353527578753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2725688590822276073543341 1022133221558353527578753)
                  ·
                    refine ⟨766599916168765145684065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1022133221558353527578753 766599916168765145684065)
                    ·
                      refine ⟨574949937126573859263049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 766599916168765145684065 574949937126573859263049)
                      ·
                        rfl

theorem cell23_1119711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 4, 3, 2, 2].length) (baseStart_1119711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1119711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1119711 prefixEnd_1119711 := by exact prefixLift 1119711
  have htrace : WordTrace (prefixWord ++ tailWord_1119711) baseStart_1119711 baseEnd_1119711 := by
    simpa [prefixWord, tailWord_1119711, baseEnd_1119711] using wordTrace_append hprefix tailTrace_1119711
  have hstable : (prefixWord ++ tailWord_1119711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119711).length < 2 ^ (prefixWord ++ tailWord_1119711).sum := by decide
  have hdescent : baseEnd_1119711 < baseStart_1119711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119722 : List Nat := [3, 1, 3, 1, 5, 1, 1, 3, 1, 1, 3]
def baseStart_1119722 : Nat := 118140960795 + 1119722 * 2 ^ 59
def prefixEnd_1119722 : Nat := 4983230072969 + 3 ^ 40 * 1119722 * 2
def baseEnd_1119722 : Nat := 574955585413773316225499

theorem tailTrace_1119722 : CollatzResearch.WordTrace tailWord_1119722 prefixEnd_1119722 574955585413773316225499 := by
  unfold tailWord_1119722
  simp only [CollatzResearch.WordTrace]
  refine ⟨10209904112361475534462355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27226410966297268091899613 10209904112361475534462355)
  ·
    refine ⟨15314856168542213301693533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10209904112361475534462355 15314856168542213301693533)
    ·
      refine ⟨5743071063203329988135075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15314856168542213301693533 5743071063203329988135075)
      ·
        refine ⟨8614606594804994982202613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5743071063203329988135075 8614606594804994982202613)
        ·
          refine ⟨807619368262968279581495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8614606594804994982202613 807619368262968279581495)
          ·
            refine ⟨1211429052394452419372243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 807619368262968279581495 1211429052394452419372243)
            ·
              refine ⟨1817143578591678629058365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1211429052394452419372243 1817143578591678629058365)
              ·
                refine ⟨681428841971879485896887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1817143578591678629058365 681428841971879485896887)
                ·
                  refine ⟨1022143262957819228845331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 681428841971879485896887 1022143262957819228845331)
                  ·
                    refine ⟨1533214894436728843267997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1022143262957819228845331 1533214894436728843267997)
                    ·
                      refine ⟨574955585413773316225499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1533214894436728843267997 574955585413773316225499)
                      ·
                        rfl

theorem cell23_1119722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 3, 1, 1, 3].length) (baseStart_1119722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1119722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1119722 prefixEnd_1119722 := by exact prefixLift 1119722
  have htrace : WordTrace (prefixWord ++ tailWord_1119722) baseStart_1119722 baseEnd_1119722 := by
    simpa [prefixWord, tailWord_1119722, baseEnd_1119722] using wordTrace_append hprefix tailTrace_1119722
  have hstable : (prefixWord ++ tailWord_1119722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119722).length < 2 ^ (prefixWord ++ tailWord_1119722).sum := by decide
  have hdescent : baseEnd_1119722 < baseStart_1119722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119734 : List Nat := [5, 1, 1, 1, 2, 4, 9]
def baseStart_1119734 : Nat := 118140960795 + 1119734 * 2 ^ 59
def prefixEnd_1119734 : Nat := 4983230072969 + 3 ^ 40 * 1119734 * 2
def baseEnd_1119734 : Nat := 7098293175081818139203

theorem tailTrace_1119734 : CollatzResearch.WordTrace tailWord_1119734 prefixEnd_1119734 7098293175081818139203 := by
  unfold tailWord_1119734
  simp only [CollatzResearch.WordTrace]
  refine ⟨2552503382837651761705391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27226702750268285458190837 2552503382837651761705391)
  ·
    refine ⟨3828755074256477642558087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2552503382837651761705391 3828755074256477642558087)
    ·
      refine ⟨5743132611384716463837131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3828755074256477642558087 5743132611384716463837131)
      ·
        refine ⟨8614698917077074695755697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5743132611384716463837131 8614698917077074695755697)
        ·
          refine ⟨6461024187807806021816773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8614698917077074695755697 6461024187807806021816773)
          ·
            refine ⟨1211442035213963629090645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6461024187807806021816773 1211442035213963629090645)
            ·
              refine ⟨7098293175081818139203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1211442035213963629090645 7098293175081818139203)
              ·
                rfl

theorem cell23_1119734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 9].length) (baseStart_1119734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1119734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1119734 prefixEnd_1119734 := by exact prefixLift 1119734
  have htrace : WordTrace (prefixWord ++ tailWord_1119734) baseStart_1119734 baseEnd_1119734 := by
    simpa [prefixWord, tailWord_1119734, baseEnd_1119734] using wordTrace_append hprefix tailTrace_1119734
  have hstable : (prefixWord ++ tailWord_1119734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119734).length < 2 ^ (prefixWord ++ tailWord_1119734).sum := by decide
  have hdescent : baseEnd_1119734 < baseStart_1119734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119745 : List Nat := [1, 2, 4, 1, 4, 2, 1, 1, 3, 2, 2]
def baseStart_1119745 : Nat := 118140960795 + 1119745 * 2 ^ 59
def prefixEnd_1119745 : Nat := 4983230072969 + 3 ^ 40 * 1119745 * 2
def baseEnd_1119745 : Nat := 574967395468826726237893

theorem tailTrace_1119745 : CollatzResearch.WordTrace tailWord_1119745 prefixEnd_1119745 574967395468826726237893 := by
  unfold tailWord_1119745
  simp only [CollatzResearch.WordTrace]
  refine ⟨40840455328362577065936689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27226970218908384710624459 40840455328362577065936689)
  ·
    refine ⟨30630341496271932799452517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40840455328362577065936689 30630341496271932799452517)
    ·
      refine ⟨5743189030550987399897347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30630341496271932799452517 5743189030550987399897347)
      ·
        refine ⟨8614783545826481099846021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5743189030550987399897347 8614783545826481099846021)
        ·
          refine ⟨1615271914842465206221129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8614783545826481099846021 1615271914842465206221129)
          ·
            refine ⟨1211453936131848904665847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1615271914842465206221129 1211453936131848904665847)
            ·
              refine ⟨1817180904197773356998771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1211453936131848904665847 1817180904197773356998771)
              ·
                refine ⟨2725771356296660035498157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1817180904197773356998771 2725771356296660035498157)
                ·
                  refine ⟨1022164258611247513311809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2725771356296660035498157 1022164258611247513311809)
                  ·
                    refine ⟨766623193958435634983857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1022164258611247513311809 766623193958435634983857)
                    ·
                      refine ⟨574967395468826726237893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 766623193958435634983857 574967395468826726237893)
                      ·
                        rfl

theorem cell23_1119745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 1, 3, 2, 2].length) (baseStart_1119745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1119745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1119745 prefixEnd_1119745 := by exact prefixLift 1119745
  have htrace : WordTrace (prefixWord ++ tailWord_1119745) baseStart_1119745 baseEnd_1119745 := by
    simpa [prefixWord, tailWord_1119745, baseEnd_1119745] using wordTrace_append hprefix tailTrace_1119745
  have hstable : (prefixWord ++ tailWord_1119745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119745).length < 2 ^ (prefixWord ++ tailWord_1119745).sum := by decide
  have hdescent : baseEnd_1119745 < baseStart_1119745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119755 : List Nat := [1, 1, 1, 1, 9, 1, 2, 1, 2, 4]
def baseStart_1119755 : Nat := 118140960795 + 1119755 * 2 ^ 59
def prefixEnd_1119755 : Nat := 4983230072969 + 3 ^ 40 * 1119755 * 2
def baseEnd_1119755 : Nat := 191657510091790562370949

theorem tailTrace_1119755 : CollatzResearch.WordTrace tailWord_1119755 prefixEnd_1119755 191657510091790562370949 := by
  unfold tailWord_1119755
  simp only [CollatzResearch.WordTrace]
  refine ⟨40840820058326348773800719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27227213372217565849200479 40840820058326348773800719)
  ·
    refine ⟨61261230087489523160701079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40840820058326348773800719 61261230087489523160701079)
    ·
      refine ⟨91891845131234284741051619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61261230087489523160701079 91891845131234284741051619)
      ·
        refine ⟨137837767696851427111577429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91891845131234284741051619 137837767696851427111577429)
        ·
          refine ⟨807643170098738830731899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 137837767696851427111577429 807643170098738830731899)
          ·
            refine ⟨1211464755148108246097849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 807643170098738830731899 1211464755148108246097849)
            ·
              refine ⟨908598566361081184573387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1211464755148108246097849 908598566361081184573387)
              ·
                refine ⟨1362897849541621776860081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 908598566361081184573387 1362897849541621776860081)
                ·
                  refine ⟨1022173387156216332645061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1362897849541621776860081 1022173387156216332645061)
                  ·
                    refine ⟨191657510091790562370949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1022173387156216332645061 191657510091790562370949)
                    ·
                      rfl

theorem cell23_1119755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 2, 1, 2, 4].length) (baseStart_1119755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1119755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1119755 prefixEnd_1119755 := by exact prefixLift 1119755
  have htrace : WordTrace (prefixWord ++ tailWord_1119755) baseStart_1119755 baseEnd_1119755 := by
    simpa [prefixWord, tailWord_1119755, baseEnd_1119755] using wordTrace_append hprefix tailTrace_1119755
  have hstable : (prefixWord ++ tailWord_1119755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119755).length < 2 ^ (prefixWord ++ tailWord_1119755).sum := by decide
  have hdescent : baseEnd_1119755 < baseStart_1119755 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119761 : List Nat := [1, 2, 2, 1, 1, 2, 5, 3, 2, 1, 3]
def baseStart_1119761 : Nat := 118140960795 + 1119761 * 2 ^ 59
def prefixEnd_1119761 : Nat := 4983230072969 + 3 ^ 40 * 1119761 * 2
def baseEnd_1119761 : Nat := 574975611159298663637819

theorem tailTrace_1119761 : CollatzResearch.WordTrace tailWord_1119761 prefixEnd_1119761 574975611159298663637819 := by
  unfold tailWord_1119761
  simp only [CollatzResearch.WordTrace]
  refine ⟨40841038896304611798519137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27227359264203074532346091 40841038896304611798519137)
  ·
    refine ⟨30630779172228458848889353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40841038896304611798519137 30630779172228458848889353)
    ·
      refine ⟨22973084379171344136667015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30630779172228458848889353 22973084379171344136667015)
      ·
        refine ⟨34459626568757016205000523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22973084379171344136667015 34459626568757016205000523)
        ·
          refine ⟨51689439853135524307500785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34459626568757016205000523 51689439853135524307500785)
          ·
            refine ⟨38767079889851643230625589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51689439853135524307500785 38767079889851643230625589)
            ·
              refine ⟨3634413739673591552871149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38767079889851643230625589 3634413739673591552871149)
              ·
                refine ⟨1362905152377596832326681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3634413739673591552871149 1362905152377596832326681)
                ·
                  refine ⟨1022178864283197624245011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1362905152377596832326681 1022178864283197624245011)
                  ·
                    refine ⟨1533268296424796436367517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1022178864283197624245011 1533268296424796436367517)
                    ·
                      refine ⟨574975611159298663637819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1533268296424796436367517 574975611159298663637819)
                      ·
                        rfl

theorem cell23_1119761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 3, 2, 1, 3].length) (baseStart_1119761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1119761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1119761 prefixEnd_1119761 := by exact prefixLift 1119761
  have htrace : WordTrace (prefixWord ++ tailWord_1119761) baseStart_1119761 baseEnd_1119761 := by
    simpa [prefixWord, tailWord_1119761, baseEnd_1119761] using wordTrace_append hprefix tailTrace_1119761
  have hstable : (prefixWord ++ tailWord_1119761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119761).length < 2 ^ (prefixWord ++ tailWord_1119761).sum := by decide
  have hdescent : baseEnd_1119761 < baseStart_1119761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119818 : List Nat := [3, 1, 2, 1, 1, 3, 1, 5, 2, 2, 2]
def baseStart_1119818 : Nat := 118140960795 + 1119818 * 2 ^ 59
def prefixEnd_1119818 : Nat := 4983230072969 + 3 ^ 40 * 1119818 * 2
def baseEnd_1119818 : Nat := 575004879556604940625057

theorem tailTrace_1119818 : CollatzResearch.WordTrace tailWord_1119818 prefixEnd_1119818 575004879556604940625057 := by
  unfold tailWord_1119818
  simp only [CollatzResearch.WordTrace]
  refine ⟨10210779464274527633336027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27228745238065407022229405 10210779464274527633336027)
  ·
    refine ⟨15316169196411791450004041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10210779464274527633336027 15316169196411791450004041)
    ·
      refine ⟨11487126897308843587503031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15316169196411791450004041 11487126897308843587503031)
      ·
        refine ⟨17230690345963265381254547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11487126897308843587503031 17230690345963265381254547)
        ·
          refine ⟨25846035518944898071881821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17230690345963265381254547 25846035518944898071881821)
          ·
            refine ⟨9692263319604336776955683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25846035518944898071881821 9692263319604336776955683)
            ·
              refine ⟨14538394979406505165433525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9692263319604336776955683 14538394979406505165433525)
              ·
                refine ⟨1362974529319359859259393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14538394979406505165433525 1362974529319359859259393)
                ·
                  refine ⟨1022230896989519894444545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1362974529319359859259393 1022230896989519894444545)
                  ·
                    refine ⟨766673172742139920833409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1022230896989519894444545 766673172742139920833409)
                    ·
                      refine ⟨575004879556604940625057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 766673172742139920833409 575004879556604940625057)
                      ·
                        rfl

theorem cell23_1119818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 5, 2, 2, 2].length) (baseStart_1119818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1119818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1119818 prefixEnd_1119818 := by exact prefixLift 1119818
  have htrace : WordTrace (prefixWord ++ tailWord_1119818) baseStart_1119818 baseEnd_1119818 := by
    simpa [prefixWord, tailWord_1119818, baseEnd_1119818] using wordTrace_append hprefix tailTrace_1119818
  have hstable : (prefixWord ++ tailWord_1119818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119818).length < 2 ^ (prefixWord ++ tailWord_1119818).sum := by decide
  have hdescent : baseEnd_1119818 < baseStart_1119818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119841 : List Nat := [1, 2, 3, 1, 1, 3, 4, 3, 5]
def baseStart_1119841 : Nat := 118140960795 + 1119841 * 2 ^ 59
def prefixEnd_1119841 : Nat := 4983230072969 + 3 ^ 40 * 1119841 * 2
def baseEnd_1119841 : Nat := 63890743290184261181939

theorem tailTrace_1119841 : CollatzResearch.WordTrace tailWord_1119841 prefixEnd_1119841 63890743290184261181939 := by
  unfold tailWord_1119841
  simp only [CollatzResearch.WordTrace]
  refine ⟨40843956736014785461431377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27229304490676523640954251 40843956736014785461431377)
  ·
    refine ⟨30632967552011089096073533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40843956736014785461431377 30632967552011089096073533)
    ·
      refine ⟨11487362832004158411027575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30632967552011089096073533 11487362832004158411027575)
      ·
        refine ⟨17231044248006237616541363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11487362832004158411027575 17231044248006237616541363)
        ·
          refine ⟨25846566372009356424812045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17231044248006237616541363 25846566372009356424812045)
          ·
            refine ⟨9692462389503508659304517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25846566372009356424812045 9692462389503508659304517)
            ·
              refine ⟨1817336698031907873619597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9692462389503508659304517 1817336698031907873619597)
              ·
                refine ⟨681501261761965452607349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1817336698031907873619597 681501261761965452607349)
                ·
                  refine ⟨63890743290184261181939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 681501261761965452607349 63890743290184261181939)
                  ·
                    rfl

theorem cell23_1119841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 3, 5].length) (baseStart_1119841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1119841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1119841 prefixEnd_1119841 := by exact prefixLift 1119841
  have htrace : WordTrace (prefixWord ++ tailWord_1119841) baseStart_1119841 baseEnd_1119841 := by
    simpa [prefixWord, tailWord_1119841, baseEnd_1119841] using wordTrace_append hprefix tailTrace_1119841
  have hstable : (prefixWord ++ tailWord_1119841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119841).length < 2 ^ (prefixWord ++ tailWord_1119841).sum := by decide
  have hdescent : baseEnd_1119841 < baseStart_1119841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119892 : List Nat := [2, 4, 2, 2, 3, 1, 1, 3, 5]
def baseStart_1119892 : Nat := 118140960795 + 1119892 * 2 ^ 59
def prefixEnd_1119892 : Nat := 4983230072969 + 3 ^ 40 * 1119892 * 2
def baseEnd_1119892 : Nat := 63893653013893072344413

theorem tailTrace_1119892 : CollatzResearch.WordTrace tailWord_1119892 prefixEnd_1119892 63893653013893072344413 := by
  unfold tailWord_1119892
  simp only [CollatzResearch.WordTrace]
  refine ⟨20422908429415010585768965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27230544572553347447691953 20422908429415010585768965)
  ·
    refine ⟨3829295330515314484831681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20422908429415010585768965 3829295330515314484831681)
    ·
      refine ⟨2871971497886485863623761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3829295330515314484831681 2871971497886485863623761)
      ·
        refine ⟨2153978623414864397717821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2871971497886485863623761 2153978623414864397717821)
        ·
          refine ⟨807741983780574149144183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2153978623414864397717821 807741983780574149144183)
          ·
            refine ⟨1211612975670861223716275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 807741983780574149144183 1211612975670861223716275)
            ·
              refine ⟨1817419463506291835574413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1211612975670861223716275 1817419463506291835574413)
              ·
                refine ⟨681532298814859438340405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1817419463506291835574413 681532298814859438340405)
                ·
                  refine ⟨63893653013893072344413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 681532298814859438340405 63893653013893072344413)
                  ·
                    rfl

theorem cell23_1119892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 3, 5].length) (baseStart_1119892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1119892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1119892 prefixEnd_1119892 := by exact prefixLift 1119892
  have htrace : WordTrace (prefixWord ++ tailWord_1119892) baseStart_1119892 baseEnd_1119892 := by
    simpa [prefixWord, tailWord_1119892, baseEnd_1119892] using wordTrace_append hprefix tailTrace_1119892
  have hstable : (prefixWord ++ tailWord_1119892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119892).length < 2 ^ (prefixWord ++ tailWord_1119892).sum := by decide
  have hdescent : baseEnd_1119892 < baseStart_1119892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119942 : List Nat := [6, 1, 2, 1, 1, 2, 2, 1, 2, 1, 4]
def baseStart_1119942 : Nat := 118140960795 + 1119942 * 2 ^ 59
def prefixEnd_1119942 : Nat := 4983230072969 + 3 ^ 40 * 1119942 * 2
def baseEnd_1119942 : Nat := 575068551157762455474487

theorem tailTrace_1119942 : CollatzResearch.WordTrace tailWord_1119942 prefixEnd_1119942 575068551157762455474487 := by
  unfold tailWord_1119942
  simp only [CollatzResearch.WordTrace]
  refine ⟨1276488765895277490964315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 27231760339099253140572053 1276488765895277490964315)
  ·
    refine ⟨1914733148842916236446473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1276488765895277490964315 1914733148842916236446473)
    ·
      refine ⟨1436049861632187177334855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1914733148842916236446473 1436049861632187177334855)
      ·
        refine ⟨2154074792448280766002283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1436049861632187177334855 2154074792448280766002283)
        ·
          refine ⟨3231112188672421149003425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2154074792448280766002283 3231112188672421149003425)
          ·
            refine ⟨2423334141504315861752569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3231112188672421149003425 2423334141504315861752569)
            ·
              refine ⟨1817500606128236896314427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2423334141504315861752569 1817500606128236896314427)
              ·
                refine ⟨2726250909192355344471641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1817500606128236896314427 2726250909192355344471641)
                ·
                  refine ⟨2044688181894266508353731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2726250909192355344471641 2044688181894266508353731)
                  ·
                    refine ⟨3067032272841399762530597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2044688181894266508353731 3067032272841399762530597)
                    ·
                      refine ⟨575068551157762455474487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3067032272841399762530597 575068551157762455474487)
                      ·
                        rfl

theorem cell23_1119942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_1119942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1119942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1119942 prefixEnd_1119942 := by exact prefixLift 1119942
  have htrace : WordTrace (prefixWord ++ tailWord_1119942) baseStart_1119942 baseEnd_1119942 := by
    simpa [prefixWord, tailWord_1119942, baseEnd_1119942] using wordTrace_append hprefix tailTrace_1119942
  have hstable : (prefixWord ++ tailWord_1119942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119942).length < 2 ^ (prefixWord ++ tailWord_1119942).sum := by decide
  have hdescent : baseEnd_1119942 < baseStart_1119942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119951 : List Nat := [1, 1, 2, 1, 1, 3, 1, 5, 1, 5, 2]
def baseStart_1119951 : Nat := 118140960795 + 1119951 * 2 ^ 59
def prefixEnd_1119951 : Nat := 4983230072969 + 3 ^ 40 * 1119951 * 2
def baseEnd_1119951 : Nat := 575073172483652920261945

theorem tailTrace_1119951 : CollatzResearch.WordTrace tailWord_1119951 prefixEnd_1119951 575073172483652920261945 := by
  unfold tailWord_1119951
  simp only [CollatzResearch.WordTrace]
  refine ⟨40847968765616274247935707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27231979177077516165290471 40847968765616274247935707)
  ·
    refine ⟨61271953148424411371903561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40847968765616274247935707 61271953148424411371903561)
    ·
      refine ⟨45953964861318308528927671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61271953148424411371903561 45953964861318308528927671)
      ·
        refine ⟨68930947291977462793391507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45953964861318308528927671 68930947291977462793391507)
        ·
          refine ⟨103396420937966194190087261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68930947291977462793391507 103396420937966194190087261)
          ·
            refine ⟨38773657851737322821282723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103396420937966194190087261 38773657851737322821282723)
            ·
              refine ⟨58160486777605984231924085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38773657851737322821282723 58160486777605984231924085)
              ·
                refine ⟨5452545635400561021742883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 58160486777605984231924085 5452545635400561021742883)
                ·
                  refine ⟨8178818453100841532614325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5452545635400561021742883 8178818453100841532614325)
                  ·
                    refine ⟨766764229978203893682593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8178818453100841532614325 766764229978203893682593)
                    ·
                      refine ⟨575073172483652920261945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 766764229978203893682593 575073172483652920261945)
                      ·
                        rfl

theorem cell23_1119951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 5, 2].length) (baseStart_1119951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1119951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1119951 prefixEnd_1119951 := by exact prefixLift 1119951
  have htrace : WordTrace (prefixWord ++ tailWord_1119951) baseStart_1119951 baseEnd_1119951 := by
    simpa [prefixWord, tailWord_1119951, baseEnd_1119951] using wordTrace_append hprefix tailTrace_1119951
  have hstable : (prefixWord ++ tailWord_1119951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119951).length < 2 ^ (prefixWord ++ tailWord_1119951).sum := by decide
  have hdescent : baseEnd_1119951 < baseStart_1119951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119965 : List Nat := [1, 4, 3, 3, 1, 1, 2, 2, 6]
def baseStart_1119965 : Nat := 118140960795 + 1119965 * 2 ^ 59
def prefixEnd_1119965 : Nat := 4983230072969 + 3 ^ 40 * 1119965 * 2
def baseEnd_1119965 : Nat := 63897817912535096165209

theorem tailTrace_1119965 : CollatzResearch.WordTrace tailWord_1119965 prefixEnd_1119965 63897817912535096165209 := by
  unfold tailWord_1119965
  simp only [CollatzResearch.WordTrace]
  refine ⟨40848479387565554638945349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27232319591710369759296899 40848479387565554638945349)
  ·
    refine ⟨7659089885168541494802253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40848479387565554638945349 7659089885168541494802253)
    ·
      refine ⟨2872158706938203060550845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7659089885168541494802253 2872158706938203060550845)
      ·
        refine ⟨1077059515101826147706567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2872158706938203060550845 1077059515101826147706567)
        ·
          refine ⟨1615589272652739221559851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1077059515101826147706567 1615589272652739221559851)
          ·
            refine ⟨2423383908979108832339777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1615589272652739221559851 2423383908979108832339777)
            ·
              refine ⟨1817537931734331624254833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2423383908979108832339777 1817537931734331624254833)
              ·
                refine ⟨1363153448800748718191125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1817537931734331624254833 1363153448800748718191125)
                ·
                  refine ⟨63897817912535096165209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1363153448800748718191125 63897817912535096165209)
                  ·
                    rfl

theorem cell23_1119965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 2, 6].length) (baseStart_1119965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1119965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1119965 prefixEnd_1119965 := by exact prefixLift 1119965
  have htrace : WordTrace (prefixWord ++ tailWord_1119965) baseStart_1119965 baseEnd_1119965 := by
    simpa [prefixWord, tailWord_1119965, baseEnd_1119965] using wordTrace_append hprefix tailTrace_1119965
  have hstable : (prefixWord ++ tailWord_1119965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119965).length < 2 ^ (prefixWord ++ tailWord_1119965).sum := by decide
  have hdescent : baseEnd_1119965 < baseStart_1119965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119968 : List Nat := [2, 1, 1, 3, 1, 2, 4, 2, 2, 3, 2]
def baseStart_1119968 : Nat := 118140960795 + 1119968 * 2 ^ 59
def prefixEnd_1119968 : Nat := 4983230072969 + 3 ^ 40 * 1119968 * 2
def baseEnd_1119968 : Nat := 575081901654779353749367

theorem tailTrace_1119968 : CollatzResearch.WordTrace tailWord_1119968 prefixEnd_1119968 575081901654779353749367 := by
  unfold tailWord_1119968
  simp only [CollatzResearch.WordTrace]
  refine ⟨20424294403277343075652279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27232392537703124100869705 20424294403277343075652279)
  ·
    refine ⟨30636441604916014613478419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20424294403277343075652279 30636441604916014613478419)
    ·
      refine ⟨45954662407374021920217629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30636441604916014613478419 45954662407374021920217629)
      ·
        refine ⟨17232998402765258220081611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45954662407374021920217629 17232998402765258220081611)
        ·
          refine ⟨25849497604147887330122417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17232998402765258220081611 25849497604147887330122417)
          ·
            refine ⟨19387123203110915497591813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25849497604147887330122417 19387123203110915497591813)
            ·
              refine ⟨3635085600583296655798465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19387123203110915497591813 3635085600583296655798465)
              ·
                refine ⟨2726314200437472491848849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3635085600583296655798465 2726314200437472491848849)
                ·
                  refine ⟨2044735650328104368886637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2726314200437472491848849 2044735650328104368886637)
                  ·
                    refine ⟨766775868873039138332489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2044735650328104368886637 766775868873039138332489)
                    ·
                      refine ⟨575081901654779353749367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 766775868873039138332489 575081901654779353749367)
                      ·
                        rfl

theorem cell23_1119968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 2, 2, 3, 2].length) (baseStart_1119968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1119968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1119968 prefixEnd_1119968 := by exact prefixLift 1119968
  have htrace : WordTrace (prefixWord ++ tailWord_1119968) baseStart_1119968 baseEnd_1119968 := by
    simpa [prefixWord, tailWord_1119968, baseEnd_1119968] using wordTrace_append hprefix tailTrace_1119968
  have hstable : (prefixWord ++ tailWord_1119968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119968).length < 2 ^ (prefixWord ++ tailWord_1119968).sum := by decide
  have hdescent : baseEnd_1119968 < baseStart_1119968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119969 : List Nat := [1, 2, 3, 1, 6, 1, 2, 2, 1, 4]
def baseStart_1119969 : Nat := 118140960795 + 1119969 * 2 ^ 59
def prefixEnd_1119969 : Nat := 4983230072969 + 3 ^ 40 * 1119969 * 2
def baseEnd_1119969 : Nat := 191694138378477949945621

theorem tailTrace_1119969 : CollatzResearch.WordTrace tailWord_1119969 prefixEnd_1119969 191694138378477949945621 := by
  unfold tailWord_1119969
  simp only [CollatzResearch.WordTrace]
  refine ⟨40848625279551063322090961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27232416853034042214727307 40848625279551063322090961)
  ·
    refine ⟨30636468959663297491568221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40848625279551063322090961 30636468959663297491568221)
    ·
      refine ⟨11488675859873736559338083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30636468959663297491568221 11488675859873736559338083)
      ·
        refine ⟨17233013789810604839007125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11488675859873736559338083 17233013789810604839007125)
        ·
          refine ⟨807797521397372101828459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 17233013789810604839007125 807797521397372101828459)
          ·
            refine ⟨1211696282096058152742689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 807797521397372101828459 1211696282096058152742689)
            ·
              refine ⟨908772211572043614557017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1211696282096058152742689 908772211572043614557017)
              ·
                refine ⟨681579158679032710917763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 908772211572043614557017 681579158679032710917763)
                ·
                  refine ⟨1022368738018549066376645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 681579158679032710917763 1022368738018549066376645)
                  ·
                    refine ⟨191694138378477949945621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1022368738018549066376645 191694138378477949945621)
                    ·
                      rfl

theorem cell23_1119969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 2, 2, 1, 4].length) (baseStart_1119969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1119969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1119969 prefixEnd_1119969 := by exact prefixLift 1119969
  have htrace : WordTrace (prefixWord ++ tailWord_1119969) baseStart_1119969 baseEnd_1119969 := by
    simpa [prefixWord, tailWord_1119969, baseEnd_1119969] using wordTrace_append hprefix tailTrace_1119969
  have hstable : (prefixWord ++ tailWord_1119969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119969).length < 2 ^ (prefixWord ++ tailWord_1119969).sum := by decide
  have hdescent : baseEnd_1119969 < baseStart_1119969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120011 : List Nat := [1, 1, 1, 1, 5, 1, 4, 2, 1, 2, 4]
def baseStart_1120011 : Nat := 118140960795 + 1120011 * 2 ^ 59
def prefixEnd_1120011 : Nat := 4983230072969 + 3 ^ 40 * 1120011 * 2
def baseEnd_1120011 : Nat := 575103981322922685511669

theorem tailTrace_1120011 : CollatzResearch.WordTrace tailWord_1120011 prefixEnd_1120011 575103981322922685511669 := by
  unfold tailWord_1120011
  simp only [CollatzResearch.WordTrace]
  refine ⟨40850157145398904495119887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27233438096932602996746591 40850157145398904495119887)
  ·
    refine ⟨61275235718098356742679831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40850157145398904495119887 61275235718098356742679831)
    ·
      refine ⟨91912853577147535114019747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61275235718098356742679831 91912853577147535114019747)
      ·
        refine ⟨137869280365721302671029621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91912853577147535114019747 137869280365721302671029621)
        ·
          refine ⟨12925245034286372125409027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 137869280365721302671029621 12925245034286372125409027)
          ·
            refine ⟨19387867551429558188113541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12925245034286372125409027 19387867551429558188113541)
            ·
              refine ⟨3635225165893042160271289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19387867551429558188113541 3635225165893042160271289)
              ·
                refine ⟨2726418874419781620203467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3635225165893042160271289 2726418874419781620203467)
                ·
                  refine ⟨4089628311629672430305201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2726418874419781620203467 4089628311629672430305201)
                  ·
                    refine ⟨3067221233722254322728901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4089628311629672430305201 3067221233722254322728901)
                    ·
                      refine ⟨575103981322922685511669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3067221233722254322728901 575103981322922685511669)
                      ·
                        rfl

theorem cell23_1120011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 2, 1, 2, 4].length) (baseStart_1120011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1120011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1120011 prefixEnd_1120011 := by exact prefixLift 1120011
  have htrace : WordTrace (prefixWord ++ tailWord_1120011) baseStart_1120011 baseEnd_1120011 := by
    simpa [prefixWord, tailWord_1120011, baseEnd_1120011] using wordTrace_append hprefix tailTrace_1120011
  have hstable : (prefixWord ++ tailWord_1120011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120011).length < 2 ^ (prefixWord ++ tailWord_1120011).sum := by decide
  have hdescent : baseEnd_1120011 < baseStart_1120011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120032 : List Nat := [2, 1, 1, 5, 1, 1, 1, 6, 1, 2, 2]
def baseStart_1120032 : Nat := 118140960795 + 1120032 * 2 ^ 59
def prefixEnd_1120032 : Nat := 4983230072969 + 3 ^ 40 * 1120032 * 2
def baseEnd_1120032 : Nat := 575114764416667103349073

theorem tailTrace_1120032 : CollatzResearch.WordTrace tailWord_1120032 prefixEnd_1120032 575114764416667103349073 := by
  unfold tailWord_1120032
  simp only [CollatzResearch.WordTrace]
  refine ⟨20425461539161412540817175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27233948718881883387756233 20425461539161412540817175)
  ·
    refine ⟨30638192308742118811225763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20425461539161412540817175 30638192308742118811225763)
    ·
      refine ⟨45957288463113178216838645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30638192308742118811225763 45957288463113178216838645)
      ·
        refine ⟨4308495793416860457828623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45957288463113178216838645 4308495793416860457828623)
        ·
          refine ⟨6462743690125290686742935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4308495793416860457828623 6462743690125290686742935)
          ·
            refine ⟨9694115535187936030114403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6462743690125290686742935 9694115535187936030114403)
            ·
              refine ⟨14541173302781904045171605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9694115535187936030114403 14541173302781904045171605)
              ·
                refine ⟨681617498567901752117419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14541173302781904045171605 681617498567901752117419)
                ·
                  refine ⟨1022426247851852628176129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 681617498567901752117419 1022426247851852628176129)
                  ·
                    refine ⟨766819685888889471132097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1022426247851852628176129 766819685888889471132097)
                    ·
                      refine ⟨575114764416667103349073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 766819685888889471132097 575114764416667103349073)
                      ·
                        rfl

theorem cell23_1120032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 6, 1, 2, 2].length) (baseStart_1120032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1120032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1120032 prefixEnd_1120032 := by exact prefixLift 1120032
  have htrace : WordTrace (prefixWord ++ tailWord_1120032) baseStart_1120032 baseEnd_1120032 := by
    simpa [prefixWord, tailWord_1120032, baseEnd_1120032] using wordTrace_append hprefix tailTrace_1120032
  have hstable : (prefixWord ++ tailWord_1120032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120032).length < 2 ^ (prefixWord ++ tailWord_1120032).sum := by decide
  have hdescent : baseEnd_1120032 < baseStart_1120032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120052 : List Nat := [2, 5, 1, 1, 2, 2, 2, 2, 1, 2, 3]
def baseStart_1120052 : Nat := 118140960795 + 1120052 * 2 ^ 59
def prefixEnd_1120052 : Nat := 4983230072969 + 3 ^ 40 * 1120052 * 2
def baseEnd_1120052 : Nat := 575125034029757025098981

theorem tailTrace_1120052 : CollatzResearch.WordTrace tailWord_1120052 prefixEnd_1120052 575125034029757025098981 := by
  unfold tailWord_1120052
  simp only [CollatzResearch.WordTrace]
  refine ⟨20425826269125184248681205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27234435025500245664908273 20425826269125184248681205)
  ·
    refine ⟨1914921212730486023313863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20425826269125184248681205 1914921212730486023313863)
    ·
      refine ⟨2872381819095729034970795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1914921212730486023313863 2872381819095729034970795)
      ·
        refine ⟨4308572728643593552456193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2872381819095729034970795 4308572728643593552456193)
        ·
          refine ⟨3231429546482695164342145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4308572728643593552456193 3231429546482695164342145)
          ·
            refine ⟨2423572159862021373256609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3231429546482695164342145 2423572159862021373256609)
            ·
              refine ⟨1817679119896516029942457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2423572159862021373256609 1817679119896516029942457)
              ·
                refine ⟨1363259339922387022456843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1817679119896516029942457 1363259339922387022456843)
                ·
                  refine ⟨2044889009883580533685265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1363259339922387022456843 2044889009883580533685265)
                  ·
                    refine ⟨1533666757412685400263949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2044889009883580533685265 1533666757412685400263949)
                    ·
                      refine ⟨575125034029757025098981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1533666757412685400263949 575125034029757025098981)
                      ·
                        rfl

theorem cell23_1120052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_1120052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1120052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1120052 prefixEnd_1120052 := by exact prefixLift 1120052
  have htrace : WordTrace (prefixWord ++ tailWord_1120052) baseStart_1120052 baseEnd_1120052 := by
    simpa [prefixWord, tailWord_1120052, baseEnd_1120052] using wordTrace_append hprefix tailTrace_1120052
  have hstable : (prefixWord ++ tailWord_1120052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120052).length < 2 ^ (prefixWord ++ tailWord_1120052).sum := by decide
  have hdescent : baseEnd_1120052 < baseStart_1120052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120099 : List Nat := [1, 1, 1, 5, 4, 2, 2, 1, 2, 1, 3]
def baseStart_1120099 : Nat := 118140960795 + 1120099 * 2 ^ 59
def prefixEnd_1120099 : Nat := 4983230072969 + 3 ^ 40 * 1120099 * 2
def baseEnd_1120099 : Nat := 575149167620518341211265

theorem tailTrace_1120099 : CollatzResearch.WordTrace tailWord_1120099 prefixEnd_1120099 575149167620518341211265 := by
  unfold tailWord_1120099
  simp only [CollatzResearch.WordTrace]
  refine ⟨40853366769080095524323351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27235577846053397016215567 40853366769080095524323351)
  ·
    refine ⟨61280050153620143286485027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40853366769080095524323351 61280050153620143286485027)
    ·
      refine ⟨91920075230430214929727541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61280050153620143286485027 91920075230430214929727541)
      ·
        refine ⟨8617507052852832649661957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 91920075230430214929727541 8617507052852832649661957)
        ·
          refine ⟨1615782572409906121811617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8617507052852832649661957 1615782572409906121811617)
          ·
            refine ⟨1211836929307429591358713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1615782572409906121811617 1211836929307429591358713)
            ·
              refine ⟨908877696980572193519035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1211836929307429591358713 908877696980572193519035)
              ·
                refine ⟨1363316545470858290278553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 908877696980572193519035 1363316545470858290278553)
                ·
                  refine ⟨1022487409103143717708915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1363316545470858290278553 1022487409103143717708915)
                  ·
                    refine ⟨1533731113654715576563373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1022487409103143717708915 1533731113654715576563373)
                    ·
                      refine ⟨575149167620518341211265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1533731113654715576563373 575149167620518341211265)
                      ·
                        rfl

theorem cell23_1120099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 2, 1, 2, 1, 3].length) (baseStart_1120099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1120099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1120099 prefixEnd_1120099 := by exact prefixLift 1120099
  have htrace : WordTrace (prefixWord ++ tailWord_1120099) baseStart_1120099 baseEnd_1120099 := by
    simpa [prefixWord, tailWord_1120099, baseEnd_1120099] using wordTrace_append hprefix tailTrace_1120099
  have hstable : (prefixWord ++ tailWord_1120099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120099).length < 2 ^ (prefixWord ++ tailWord_1120099).sum := by decide
  have hdescent : baseEnd_1120099 < baseStart_1120099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120101 : List Nat := [1, 3, 1, 3, 1, 1, 1, 3, 1, 4, 4]
def baseStart_1120101 : Nat := 118140960795 + 1120101 * 2 ^ 59
def prefixEnd_1120101 : Nat := 4983230072969 + 3 ^ 40 * 1120101 * 2
def baseEnd_1120101 : Nat := 575150194581827333386255

theorem tailTrace_1120101 : CollatzResearch.WordTrace tailWord_1120101 prefixEnd_1120101 575150194581827333386255 := by
  unfold tailWord_1120101
  simp only [CollatzResearch.WordTrace]
  refine ⟨40853439715072849865896157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27235626476715233243930771 40853439715072849865896157)
  ·
    refine ⟨15320039893152318699711059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40853439715072849865896157 15320039893152318699711059)
    ·
      refine ⟨22980059839728478049566589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15320039893152318699711059 22980059839728478049566589)
      ·
        refine ⟨8617522439898179268587471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22980059839728478049566589 8617522439898179268587471)
        ·
          refine ⟨12926283659847268902881207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8617522439898179268587471 12926283659847268902881207)
          ·
            refine ⟨19389425489770903354321811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12926283659847268902881207 19389425489770903354321811)
            ·
              refine ⟨29084138234656355031482717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19389425489770903354321811 29084138234656355031482717)
              ·
                refine ⟨10906551837996133136806019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29084138234656355031482717 10906551837996133136806019)
                ·
                  refine ⟨16359827756994199705209029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10906551837996133136806019 16359827756994199705209029)
                  ·
                    refine ⟨3067467704436412444726693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16359827756994199705209029 3067467704436412444726693)
                    ·
                      refine ⟨575150194581827333386255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3067467704436412444726693 575150194581827333386255)
                      ·
                        rfl

theorem cell23_1120101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_1120101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1120101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1120101 prefixEnd_1120101 := by exact prefixLift 1120101
  have htrace : WordTrace (prefixWord ++ tailWord_1120101) baseStart_1120101 baseEnd_1120101 := by
    simpa [prefixWord, tailWord_1120101, baseEnd_1120101] using wordTrace_append hprefix tailTrace_1120101
  have hstable : (prefixWord ++ tailWord_1120101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120101).length < 2 ^ (prefixWord ++ tailWord_1120101).sum := by decide
  have hdescent : baseEnd_1120101 < baseStart_1120101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120126 : List Nat := [4, 2, 3, 1, 1, 2, 3, 1, 1, 3, 2]
def baseStart_1120126 : Nat := 118140960795 + 1120126 * 2 ^ 59
def prefixEnd_1120126 : Nat := 4983230072969 + 3 ^ 40 * 1120126 * 2
def baseEnd_1120126 : Nat := 575163031598189735573641

theorem tailTrace_1120126 : CollatzResearch.WordTrace tailWord_1120126 prefixEnd_1120126 575163031598189735573641 := by
  unfold tailWord_1120126
  simp only [CollatzResearch.WordTrace]
  refine ⟨5106793942497784891944529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27236234359988186090370821 5106793942497784891944529)
  ·
    refine ⟨3830095456873338668958397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5106793942497784891944529 3830095456873338668958397)
    ·
      refine ⟨1436285796327502000859399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3830095456873338668958397 1436285796327502000859399)
      ·
        refine ⟨2154428694491253001289099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1436285796327502000859399 2154428694491253001289099)
        ·
          refine ⟨3231643041736879501933649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2154428694491253001289099 3231643041736879501933649)
          ·
            refine ⟨2423732281302659626450237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3231643041736879501933649 2423732281302659626450237)
            ·
              refine ⟨908899605488497359918839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2423732281302659626450237 908899605488497359918839)
              ·
                refine ⟨1363349408232746039878259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 908899605488497359918839 1363349408232746039878259)
                ·
                  refine ⟨2045024112349119059817389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1363349408232746039878259 2045024112349119059817389)
                  ·
                    refine ⟨766884042130919647431521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2045024112349119059817389 766884042130919647431521)
                    ·
                      refine ⟨575163031598189735573641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 766884042130919647431521 575163031598189735573641)
                      ·
                        rfl

theorem cell23_1120126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_1120126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1120126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1120126 prefixEnd_1120126 := by exact prefixLift 1120126
  have htrace : WordTrace (prefixWord ++ tailWord_1120126) baseStart_1120126 baseEnd_1120126 := by
    simpa [prefixWord, tailWord_1120126, baseEnd_1120126] using wordTrace_append hprefix tailTrace_1120126
  have hstable : (prefixWord ++ tailWord_1120126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120126).length < 2 ^ (prefixWord ++ tailWord_1120126).sum := by decide
  have hdescent : baseEnd_1120126 < baseStart_1120126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120128 : List Nat := [2, 1, 1, 2, 1, 2, 4, 5, 5]
def baseStart_1120128 : Nat := 118140960795 + 1120128 * 2 ^ 59
def prefixEnd_1120128 : Nat := 4983230072969 + 3 ^ 40 * 1120128 * 2
def baseEnd_1120128 : Nat := 63907117617722080860959

theorem tailTrace_1120128 : CollatzResearch.WordTrace tailWord_1120128 prefixEnd_1120128 63907117617722080860959 := by
  unfold tailWord_1120128
  simp only [CollatzResearch.WordTrace]
  refine ⟨20427212242987516738564519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27236282990650022318086025 20427212242987516738564519)
  ·
    refine ⟨30640818364481275107846779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20427212242987516738564519 30640818364481275107846779)
    ·
      refine ⟨45961227546721912661770169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30640818364481275107846779 45961227546721912661770169)
      ·
        refine ⟨34470920660041434496327627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45961227546721912661770169 34470920660041434496327627)
        ·
          refine ⟨51706380990062151744491441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34470920660041434496327627 51706380990062151744491441)
          ·
            refine ⟨38779785742546613808368581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51706380990062151744491441 38779785742546613808368581)
            ·
              refine ⟨7271209826727490089069109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38779785742546613808368581 7271209826727490089069109)
              ·
                refine ⟨681675921255702195850229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7271209826727490089069109 681675921255702195850229)
                ·
                  refine ⟨63907117617722080860959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 681675921255702195850229 63907117617722080860959)
                  ·
                    rfl

theorem cell23_1120128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 5, 5].length) (baseStart_1120128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1120128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1120128 prefixEnd_1120128 := by exact prefixLift 1120128
  have htrace : WordTrace (prefixWord ++ tailWord_1120128) baseStart_1120128 baseEnd_1120128 := by
    simpa [prefixWord, tailWord_1120128, baseEnd_1120128] using wordTrace_append hprefix tailTrace_1120128
  have hstable : (prefixWord ++ tailWord_1120128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120128).length < 2 ^ (prefixWord ++ tailWord_1120128).sum := by decide
  have hdescent : baseEnd_1120128 < baseStart_1120128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120145 : List Nat := [1, 2, 2, 1, 1, 1, 8, 2, 5]
def baseStart_1120145 : Nat := 118140960795 + 1120145 * 2 ^ 59
def prefixEnd_1120145 : Nat := 4983230072969 + 3 ^ 40 * 1120145 * 2
def baseEnd_1120145 : Nat := 63908087525625017915117

theorem tailTrace_1120145 : CollatzResearch.WordTrace tailWord_1120145 prefixEnd_1120145 63908087525625017915117 := by
  unfold tailWord_1120145
  simp only [CollatzResearch.WordTrace]
  refine ⟨40855044526913445380497889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27236696351275630253665259 40855044526913445380497889)
  ·
    refine ⟨30641283395185084035373417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40855044526913445380497889 30641283395185084035373417)
    ·
      refine ⟨22980962546388813026530063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30641283395185084035373417 22980962546388813026530063)
      ·
        refine ⟨34471443819583219539795095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22980962546388813026530063 34471443819583219539795095)
        ·
          refine ⟨51707165729374829309692643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34471443819583219539795095 51707165729374829309692643)
          ·
            refine ⟨77560748594062243964538965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51707165729374829309692643 77560748594062243964538965)
            ·
              refine ⟨908915022586666921459441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 77560748594062243964538965 908915022586666921459441)
              ·
                refine ⟨681686266940000191094581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 908915022586666921459441 681686266940000191094581)
                ·
                  refine ⟨63908087525625017915117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 681686266940000191094581 63908087525625017915117)
                  ·
                    rfl

theorem cell23_1120145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 8, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 8, 2, 5].length) (baseStart_1120145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1120145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1120145 prefixEnd_1120145 := by exact prefixLift 1120145
  have htrace : WordTrace (prefixWord ++ tailWord_1120145) baseStart_1120145 baseEnd_1120145 := by
    simpa [prefixWord, tailWord_1120145, baseEnd_1120145] using wordTrace_append hprefix tailTrace_1120145
  have hstable : (prefixWord ++ tailWord_1120145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120145).length < 2 ^ (prefixWord ++ tailWord_1120145).sum := by decide
  have hdescent : baseEnd_1120145 < baseStart_1120145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120191 : List Nat := [1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 6]
def baseStart_1120191 : Nat := 118140960795 + 1120191 * 2 ^ 59
def prefixEnd_1120191 : Nat := 4983230072969 + 3 ^ 40 * 1120191 * 2
def baseEnd_1120191 : Nat := 575196407840731981260841

theorem tailTrace_1120191 : CollatzResearch.WordTrace tailWord_1120191 prefixEnd_1120191 575196407840731981260841 := by
  unfold tailWord_1120191
  simp only [CollatzResearch.WordTrace]
  refine ⟨40856722284746795236672427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27237814856497863491114951 40856722284746795236672427)
  ·
    refine ⟨61285083427120192855008641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40856722284746795236672427 61285083427120192855008641)
    ·
      refine ⟨45963812570340144641256481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61285083427120192855008641 45963812570340144641256481)
      ·
        refine ⟨34472859427755108480942361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45963812570340144641256481 34472859427755108480942361)
        ·
          refine ⟨25854644570816331360706771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34472859427755108480942361 25854644570816331360706771)
          ·
            refine ⟨38781966856224497041060157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25854644570816331360706771 38781966856224497041060157)
            ·
              refine ⟨14543237571084186390397559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38781966856224497041060157 14543237571084186390397559)
              ·
                refine ⟨21814856356626279585596339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14543237571084186390397559 21814856356626279585596339)
                ·
                  refine ⟨32722284534939419378394509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21814856356626279585596339 32722284534939419378394509)
                  ·
                    refine ⟨12270856700602282266897941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32722284534939419378394509 12270856700602282266897941)
                    ·
                      refine ⟨575196407840731981260841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12270856700602282266897941 575196407840731981260841)
                      ·
                        rfl

theorem cell23_1120191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 6].length) (baseStart_1120191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1120191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1120191 prefixEnd_1120191 := by exact prefixLift 1120191
  have htrace : WordTrace (prefixWord ++ tailWord_1120191) baseStart_1120191 baseEnd_1120191 := by
    simpa [prefixWord, tailWord_1120191, baseEnd_1120191] using wordTrace_append hprefix tailTrace_1120191
  have hstable : (prefixWord ++ tailWord_1120191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120191).length < 2 ^ (prefixWord ++ tailWord_1120191).sum := by decide
  have hdescent : baseEnd_1120191 < baseStart_1120191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120201 : List Nat := [1, 2, 1, 1, 2, 1, 2, 5, 8]
def baseStart_1120201 : Nat := 118140960795 + 1120201 * 2 ^ 59
def prefixEnd_1120201 : Nat := 4983230072969 + 3 ^ 40 * 1120201 * 2
def baseEnd_1120201 : Nat := 63911282516364104681755

theorem tailTrace_1120201 : CollatzResearch.WordTrace tailWord_1120201 prefixEnd_1120201 63911282516364104681755 := by
  unfold tailWord_1120201
  simp only [CollatzResearch.WordTrace]
  refine ⟨40857087014710566944536457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27238058009807044629690971 40857087014710566944536457)
  ·
    refine ⟨30642815261032925208402343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40857087014710566944536457 30642815261032925208402343)
    ·
      refine ⟨45964222891549387812603515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30642815261032925208402343 45964222891549387812603515)
      ·
        refine ⟨68946334337324081718905273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45964222891549387812603515 68946334337324081718905273)
        ·
          refine ⟨51709750752993061289178955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68946334337324081718905273 51709750752993061289178955)
          ·
            refine ⟨77564626129489591933768433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51709750752993061289178955 77564626129489591933768433)
            ·
              refine ⟨58173469597117193950326325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77564626129489591933768433 58173469597117193950326325)
              ·
                refine ⟨5453762774729736932843093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 58173469597117193950326325 5453762774729736932843093)
                ·
                  refine ⟨63911282516364104681755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5453762774729736932843093 63911282516364104681755)
                  ·
                    rfl

theorem cell23_1120201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 8].length) (baseStart_1120201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1120201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1120201 prefixEnd_1120201 := by exact prefixLift 1120201
  have htrace : WordTrace (prefixWord ++ tailWord_1120201) baseStart_1120201 baseEnd_1120201 := by
    simpa [prefixWord, tailWord_1120201, baseEnd_1120201] using wordTrace_append hprefix tailTrace_1120201
  have hstable : (prefixWord ++ tailWord_1120201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120201).length < 2 ^ (prefixWord ++ tailWord_1120201).sum := by decide
  have hdescent : baseEnd_1120201 < baseStart_1120201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120228 : List Nat := [2, 3, 1, 1, 1, 1, 3, 1, 2, 5, 3]
def baseStart_1120228 : Nat := 118140960795 + 1120228 * 2 ^ 59
def prefixEnd_1120228 : Nat := 4983230072969 + 3 ^ 40 * 1120228 * 2
def baseEnd_1120228 : Nat := 575215406624948336498171

theorem tailTrace_1120228 : CollatzResearch.WordTrace tailWord_1120228 prefixEnd_1120228 575215406624948336498171 := by
  unfold tailWord_1120228
  simp only [CollatzResearch.WordTrace]
  refine ⟨20429035892806375277884669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27238714523741833703846225 20429035892806375277884669)
  ·
    refine ⟨7660888459802390729206751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20429035892806375277884669 7660888459802390729206751)
    ·
      refine ⟨11491332689703586093810127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7660888459802390729206751 11491332689703586093810127)
      ·
        refine ⟨17236999034555379140715191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11491332689703586093810127 17236999034555379140715191)
        ·
          refine ⟨25855498551833068711072787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17236999034555379140715191 25855498551833068711072787)
          ·
            refine ⟨38783247827749603066609181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25855498551833068711072787 38783247827749603066609181)
            ·
              refine ⟨14543717935406101149978443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38783247827749603066609181 14543717935406101149978443)
              ·
                refine ⟨21815576903109151724967665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14543717935406101149978443 21815576903109151724967665)
                ·
                  refine ⟨16361682677331863793725749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21815576903109151724967665 16361682677331863793725749)
                  ·
                    refine ⟨1533907750999862230661789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16361682677331863793725749 1533907750999862230661789)
                    ·
                      refine ⟨575215406624948336498171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1533907750999862230661789 575215406624948336498171)
                      ·
                        rfl

theorem cell23_1120228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 2, 5, 3].length) (baseStart_1120228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1120228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1120228 prefixEnd_1120228 := by exact prefixLift 1120228
  have htrace : WordTrace (prefixWord ++ tailWord_1120228) baseStart_1120228 baseEnd_1120228 := by
    simpa [prefixWord, tailWord_1120228, baseEnd_1120228] using wordTrace_append hprefix tailTrace_1120228
  have hstable : (prefixWord ++ tailWord_1120228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120228).length < 2 ^ (prefixWord ++ tailWord_1120228).sum := by decide
  have hdescent : baseEnd_1120228 < baseStart_1120228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120282 : List Nat := [3, 1, 1, 3, 1, 5, 1, 2, 1, 5]
def baseStart_1120282 : Nat := 118140960795 + 1120282 * 2 ^ 59
def prefixEnd_1120282 : Nat := 4983230072969 + 3 ^ 40 * 1120282 * 2
def baseEnd_1120282 : Nat := 191747711526763708407641

theorem tailTrace_1120282 : CollatzResearch.WordTrace tailWord_1120282 prefixEnd_1120282 191747711526763708407641 := by
  unfold tailWord_1120282
  simp only [CollatzResearch.WordTrace]
  refine ⟨10215010331854279444558775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27240027551611411852156733 10215010331854279444558775)
  ·
    refine ⟨15322515497781419166838163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10215010331854279444558775 15322515497781419166838163)
    ·
      refine ⟨22983773246672128750257245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15322515497781419166838163 22983773246672128750257245)
      ·
        refine ⟨8618914967502048281346467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22983773246672128750257245 8618914967502048281346467)
        ·
          refine ⟨12928372451253072422019701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8618914967502048281346467 12928372451253072422019701)
          ·
            refine ⟨1212034917304975539564347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12928372451253072422019701 1212034917304975539564347)
            ·
              refine ⟨1818052375957463309346521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1212034917304975539564347 1818052375957463309346521)
              ·
                refine ⟨1363539281968097482009891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1818052375957463309346521 1363539281968097482009891)
                ·
                  refine ⟨2045308922952146223014837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1363539281968097482009891 2045308922952146223014837)
                  ·
                    refine ⟨191747711526763708407641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2045308922952146223014837 191747711526763708407641)
                    ·
                      rfl

theorem cell23_1120282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 2, 1, 5].length) (baseStart_1120282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1120282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1120282 prefixEnd_1120282 := by exact prefixLift 1120282
  have htrace : WordTrace (prefixWord ++ tailWord_1120282) baseStart_1120282 baseEnd_1120282 := by
    simpa [prefixWord, tailWord_1120282, baseEnd_1120282] using wordTrace_append hprefix tailTrace_1120282
  have hstable : (prefixWord ++ tailWord_1120282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120282).length < 2 ^ (prefixWord ++ tailWord_1120282).sum := by decide
  have hdescent : baseEnd_1120282 < baseStart_1120282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120289 : List Nat := [1, 2, 3, 2, 4, 1, 2, 1, 2, 3, 2]
def baseStart_1120289 : Nat := 118140960795 + 1120289 * 2 ^ 59
def prefixEnd_1120289 : Nat := 4983230072969 + 3 ^ 40 * 1120289 * 2
def baseEnd_1120289 : Nat := 575246728944872597835391

theorem tailTrace_1120289 : CollatzResearch.WordTrace tailWord_1120289 prefixEnd_1120289 575246728944872597835391 := by
  unfold tailWord_1120289
  simp only [CollatzResearch.WordTrace]
  refine ⟨40860296638391757973739921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27240197758927838649159947 40860296638391757973739921)
  ·
    refine ⟨30645222478793818480304941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40860296638391757973739921 30645222478793818480304941)
    ·
      refine ⟨11491958429547681930114353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30645222478793818480304941 11491958429547681930114353)
      ·
        refine ⟨8618968822160761447585765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11491958429547681930114353 8618968822160761447585765)
        ·
          refine ⟨1616056654155142771422331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8618968822160761447585765 1616056654155142771422331)
          ·
            refine ⟨2424084981232714157133497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1616056654155142771422331 2424084981232714157133497)
            ·
              refine ⟨1818063735924535617850123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2424084981232714157133497 1818063735924535617850123)
              ·
                refine ⟨2727095603886803426775185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1818063735924535617850123 2727095603886803426775185)
                ·
                  refine ⟨2045321702915102570081389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2727095603886803426775185 2045321702915102570081389)
                  ·
                    refine ⟨766995638593163463780521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2045321702915102570081389 766995638593163463780521)
                    ·
                      refine ⟨575246728944872597835391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 766995638593163463780521 575246728944872597835391)
                      ·
                        rfl

theorem cell23_1120289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 1, 2, 3, 2].length) (baseStart_1120289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1120289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1120289 prefixEnd_1120289 := by exact prefixLift 1120289
  have htrace : WordTrace (prefixWord ++ tailWord_1120289) baseStart_1120289 baseEnd_1120289 := by
    simpa [prefixWord, tailWord_1120289, baseEnd_1120289] using wordTrace_append hprefix tailTrace_1120289
  have hstable : (prefixWord ++ tailWord_1120289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120289).length < 2 ^ (prefixWord ++ tailWord_1120289).sum := by decide
  have hdescent : baseEnd_1120289 < baseStart_1120289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120305 : List Nat := [1, 2, 2, 3, 1, 3, 3, 1, 1, 1, 5]
def baseStart_1120305 : Nat := 118140960795 + 1120305 * 2 ^ 59
def prefixEnd_1120305 : Nat := 4983230072969 + 3 ^ 40 * 1120305 * 2
def baseEnd_1120305 : Nat := 575254944635344535235317

theorem tailTrace_1120305 : CollatzResearch.WordTrace tailWord_1120305 prefixEnd_1120305 575254944635344535235317 := by
  unfold tailWord_1120305
  simp only [CollatzResearch.WordTrace]
  refine ⟨40860880206333792706322369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27240586804222528470881579 40860880206333792706322369)
  ·
    refine ⟨30645660154750344529741777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40860880206333792706322369 30645660154750344529741777)
    ·
      refine ⟨22984245116062758397306333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30645660154750344529741777 22984245116062758397306333)
      ·
        refine ⟨8619091918523534398989875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22984245116062758397306333 8619091918523534398989875)
        ·
          refine ⟨12928637877785301598484813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8619091918523534398989875 12928637877785301598484813)
          ·
            refine ⟨4848239204169488099431805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12928637877785301598484813 4848239204169488099431805)
            ·
              refine ⟨1818089701563558037286927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4848239204169488099431805 1818089701563558037286927)
              ·
                refine ⟨2727134552345337055930391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1818089701563558037286927 2727134552345337055930391)
                ·
                  refine ⟨4090701828518005583895587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2727134552345337055930391 4090701828518005583895587)
                  ·
                    refine ⟨6136052742777008375843381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4090701828518005583895587 6136052742777008375843381)
                    ·
                      refine ⟨575254944635344535235317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6136052742777008375843381 575254944635344535235317)
                      ·
                        rfl

theorem cell23_1120305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 1, 1, 1, 5].length) (baseStart_1120305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1120305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1120305 prefixEnd_1120305 := by exact prefixLift 1120305
  have htrace : WordTrace (prefixWord ++ tailWord_1120305) baseStart_1120305 baseEnd_1120305 := by
    simpa [prefixWord, tailWord_1120305, baseEnd_1120305] using wordTrace_append hprefix tailTrace_1120305
  have hstable : (prefixWord ++ tailWord_1120305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120305).length < 2 ^ (prefixWord ++ tailWord_1120305).sum := by decide
  have hdescent : baseEnd_1120305 < baseStart_1120305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120313 : List Nat := [1, 2, 1, 5, 3, 2, 2, 2, 1, 1, 3]
def baseStart_1120313 : Nat := 118140960795 + 1120313 * 2 ^ 59
def prefixEnd_1120313 : Nat := 4983230072969 + 3 ^ 40 * 1120313 * 2
def baseEnd_1120313 : Nat := 575259052480580503935281

theorem tailTrace_1120313 : CollatzResearch.WordTrace tailWord_1120313 prefixEnd_1120313 575259052480580503935281 := by
  unfold tailWord_1120313
  simp only [CollatzResearch.WordTrace]
  refine ⟨40861171990304810072613593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27240781326869873381742395 40861171990304810072613593)
  ·
    refine ⟨30645878992728607554460195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40861171990304810072613593 30645878992728607554460195)
    ·
      refine ⟨45968818489092911331690293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30645878992728607554460195 45968818489092911331690293)
      ·
        refine ⟨4309576733352460437345965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45968818489092911331690293 4309576733352460437345965)
        ·
          refine ⟨1616091275007172664004737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4309576733352460437345965 1616091275007172664004737)
          ·
            refine ⟨1212068456255379498003553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1616091275007172664004737 1212068456255379498003553)
            ·
              refine ⟨909051342191534623502665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1212068456255379498003553 909051342191534623502665)
              ·
                refine ⟨681788506643650967626999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 909051342191534623502665 681788506643650967626999)
                ·
                  refine ⟨1022682759965476451440499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 681788506643650967626999 1022682759965476451440499)
                  ·
                    refine ⟨1534024139948214677160749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1022682759965476451440499 1534024139948214677160749)
                    ·
                      refine ⟨575259052480580503935281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1534024139948214677160749 575259052480580503935281)
                      ·
                        rfl

theorem cell23_1120313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 2, 2, 1, 1, 3].length) (baseStart_1120313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1120313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1120313 prefixEnd_1120313 := by exact prefixLift 1120313
  have htrace : WordTrace (prefixWord ++ tailWord_1120313) baseStart_1120313 baseEnd_1120313 := by
    simpa [prefixWord, tailWord_1120313, baseEnd_1120313] using wordTrace_append hprefix tailTrace_1120313
  have hstable : (prefixWord ++ tailWord_1120313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120313).length < 2 ^ (prefixWord ++ tailWord_1120313).sum := by decide
  have hdescent : baseEnd_1120313 < baseStart_1120313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120350 : List Nat := [4, 4, 1, 1, 3, 1, 2, 1, 1, 5]
def baseStart_1120350 : Nat := 118140960795 + 1120350 * 2 ^ 59
def prefixEnd_1120350 : Nat := 4983230072969 + 3 ^ 40 * 1120350 * 2
def baseEnd_1120350 : Nat := 191759350421598953057537

theorem tailTrace_1120350 : CollatzResearch.WordTrace tailWord_1120350 prefixEnd_1120350 191759350421598953057537 := by
  unfold tailWord_1120350
  simp only [CollatzResearch.WordTrace]
  refine ⟨5107815186396345673963813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27241680994113843594473669 5107815186396345673963813)
  ·
    refine ⟨957715347449314813868215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5107815186396345673963813 957715347449314813868215)
    ·
      refine ⟨1436573021173972220802323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 957715347449314813868215 1436573021173972220802323)
      ·
        refine ⟨2154859531760958331203485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1436573021173972220802323 2154859531760958331203485)
        ·
          refine ⟨808072324410359374201307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2154859531760958331203485 808072324410359374201307)
          ·
            refine ⟨1212108486615539061301961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 808072324410359374201307 1212108486615539061301961)
            ·
              refine ⟨909081364961654295976471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1212108486615539061301961 909081364961654295976471)
              ·
                refine ⟨1363622047442481443964707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 909081364961654295976471 1363622047442481443964707)
                ·
                  refine ⟨2045433071163722165947061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1363622047442481443964707 2045433071163722165947061)
                  ·
                    refine ⟨191759350421598953057537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2045433071163722165947061 191759350421598953057537)
                    ·
                      rfl

theorem cell23_1120350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_1120350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1120350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1120350 prefixEnd_1120350 := by exact prefixLift 1120350
  have htrace : WordTrace (prefixWord ++ tailWord_1120350) baseStart_1120350 baseEnd_1120350 := by
    simpa [prefixWord, tailWord_1120350, baseEnd_1120350] using wordTrace_append hprefix tailTrace_1120350
  have hstable : (prefixWord ++ tailWord_1120350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120350).length < 2 ^ (prefixWord ++ tailWord_1120350).sum := by decide
  have hdescent : baseEnd_1120350 < baseStart_1120350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120445 : List Nat := [1, 4, 1, 2, 1, 1, 1, 1, 6, 5]
def baseStart_1120445 : Nat := 118140960795 + 1120445 * 2 ^ 59
def prefixEnd_1120445 : Nat := 4983230072969 + 3 ^ 40 * 1120445 * 2
def baseEnd_1120445 : Nat := 191775610642324662494891

theorem tailTrace_1120445 : CollatzResearch.WordTrace tailWord_1120445 prefixEnd_1120445 191775610642324662494891 := by
  unfold tailWord_1120445
  simp only [CollatzResearch.WordTrace]
  refine ⟨40865986425826596616418789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27243990950551064410945859 40865986425826596616418789)
  ·
    refine ⟨7662372454842486865578523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40865986425826596616418789 7662372454842486865578523)
    ·
      refine ⟨11493558682263730298367785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7662372454842486865578523 11493558682263730298367785)
      ·
        refine ⟨8620169011697797723775839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11493558682263730298367785 8620169011697797723775839)
        ·
          refine ⟨12930253517546696585663759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8620169011697797723775839 12930253517546696585663759)
          ·
            refine ⟨19395380276320044878495639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12930253517546696585663759 19395380276320044878495639)
            ·
              refine ⟨29093070414480067317743459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19395380276320044878495639 29093070414480067317743459)
              ·
                refine ⟨43639605621720100976615189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29093070414480067317743459 43639605621720100976615189)
                ·
                  refine ⟨2045606513518129733278837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 43639605621720100976615189 2045606513518129733278837)
                  ·
                    refine ⟨191775610642324662494891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2045606513518129733278837 191775610642324662494891)
                    ·
                      rfl

theorem cell23_1120445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 6, 5].length) (baseStart_1120445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1120445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1120445 prefixEnd_1120445 := by exact prefixLift 1120445
  have htrace : WordTrace (prefixWord ++ tailWord_1120445) baseStart_1120445 baseEnd_1120445 := by
    simpa [prefixWord, tailWord_1120445, baseEnd_1120445] using wordTrace_append hprefix tailTrace_1120445
  have hstable : (prefixWord ++ tailWord_1120445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120445).length < 2 ^ (prefixWord ++ tailWord_1120445).sum := by decide
  have hdescent : baseEnd_1120445 < baseStart_1120445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120462 : List Nat := [4, 1, 1, 1, 4, 1, 1, 3, 2, 5]
def baseStart_1120462 : Nat := 118140960795 + 1120462 * 2 ^ 59
def prefixEnd_1120462 : Nat := 4983230072969 + 3 ^ 40 * 1120462 * 2
def baseEnd_1120462 : Nat := 191778520366033473657365

theorem tailTrace_1120462 : CollatzResearch.WordTrace tailWord_1120462 prefixEnd_1120462 191778520366033473657365 := by
  unfold tailWord_1120462
  simp only [CollatzResearch.WordTrace]
  refine ⟨5108325808345626064973455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27244404311176672346525093 5108325808345626064973455)
  ·
    refine ⟨7662488712518439097460183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5108325808345626064973455 7662488712518439097460183)
    ·
      refine ⟨11493733068777658646190275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7662488712518439097460183 11493733068777658646190275)
      ·
        refine ⟨17240599603166487969285413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11493733068777658646190275 17240599603166487969285413)
        ·
          refine ⟨3232612425593716494241015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17240599603166487969285413 3232612425593716494241015)
          ·
            refine ⟨4848918638390574741361523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3232612425593716494241015 4848918638390574741361523)
            ·
              refine ⟨7273377957585862112042285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4848918638390574741361523 7273377957585862112042285)
              ·
                refine ⟨2727516734094698292015857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7273377957585862112042285 2727516734094698292015857)
                ·
                  refine ⟨2045637550571023719011893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2727516734094698292015857 2045637550571023719011893)
                  ·
                    refine ⟨191778520366033473657365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2045637550571023719011893 191778520366033473657365)
                    ·
                      rfl

theorem cell23_1120462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 3, 2, 5].length) (baseStart_1120462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1120462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1120462 prefixEnd_1120462 := by exact prefixLift 1120462
  have htrace : WordTrace (prefixWord ++ tailWord_1120462) baseStart_1120462 baseEnd_1120462 := by
    simpa [prefixWord, tailWord_1120462, baseEnd_1120462] using wordTrace_append hprefix tailTrace_1120462
  have hstable : (prefixWord ++ tailWord_1120462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120462).length < 2 ^ (prefixWord ++ tailWord_1120462).sum := by decide
  have hdescent : baseEnd_1120462 < baseStart_1120462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120465 : List Nat := [1, 2, 2, 1, 2, 2, 2, 3, 1, 3, 4]
def baseStart_1120465 : Nat := 118140960795 + 1120465 * 2 ^ 59
def prefixEnd_1120465 : Nat := 4983230072969 + 3 ^ 40 * 1120465 * 2
def baseEnd_1120465 : Nat := 575337101540063909234581

theorem tailTrace_1120465 : CollatzResearch.WordTrace tailWord_1120465 prefixEnd_1120465 575337101540063909234581 := by
  unfold tailWord_1120465
  simp only [CollatzResearch.WordTrace]
  refine ⟨40866715885754140032146849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27244477257169426688097899 40866715885754140032146849)
  ·
    refine ⟨30650036914315605024110137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40866715885754140032146849 30650036914315605024110137)
    ·
      refine ⟨22987527685736703768082603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30650036914315605024110137 22987527685736703768082603)
      ·
        refine ⟨34481291528605055652123905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22987527685736703768082603 34481291528605055652123905)
        ·
          refine ⟨25860968646453791739092929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34481291528605055652123905 25860968646453791739092929)
          ·
            refine ⟨19395726484840343804319697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25860968646453791739092929 19395726484840343804319697)
            ·
              refine ⟨14546794863630257853239773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19395726484840343804319697 14546794863630257853239773)
              ·
                refine ⟨5455048073861346694964915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14546794863630257853239773 5455048073861346694964915)
                ·
                  refine ⟨8182572110792020042447373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5455048073861346694964915 8182572110792020042447373)
                  ·
                    refine ⟨3068464541547007515917765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8182572110792020042447373 3068464541547007515917765)
                    ·
                      refine ⟨575337101540063909234581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3068464541547007515917765 575337101540063909234581)
                      ·
                        rfl

theorem cell23_1120465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 3, 4].length) (baseStart_1120465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1120465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1120465 prefixEnd_1120465 := by exact prefixLift 1120465
  have htrace : WordTrace (prefixWord ++ tailWord_1120465) baseStart_1120465 baseEnd_1120465 := by
    simpa [prefixWord, tailWord_1120465, baseEnd_1120465] using wordTrace_append hprefix tailTrace_1120465
  have hstable : (prefixWord ++ tailWord_1120465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120465).length < 2 ^ (prefixWord ++ tailWord_1120465).sum := by decide
  have hdescent : baseEnd_1120465 < baseStart_1120465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120483 : List Nat := [1, 1, 1, 8, 1, 2, 2, 2, 5]
def baseStart_1120483 : Nat := 118140960795 + 1120483 * 2 ^ 59
def prefixEnd_1120483 : Nat := 4983230072969 + 3 ^ 40 * 1120483 * 2
def baseEnd_1120483 : Nat := 63927371576871648756611

theorem tailTrace_1120483 : CollatzResearch.WordTrace tailWord_1120483 prefixEnd_1120483 63927371576871648756611 := by
  unfold tailWord_1120483
  simp only [CollatzResearch.WordTrace]
  refine ⟨40867372399688929106302103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27244914933125952737534735 40867372399688929106302103)
  ·
    refine ⟨61301058599533393659453155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40867372399688929106302103 61301058599533393659453155)
    ·
      refine ⟨91951587899300090489179733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61301058599533393659453155 91951587899300090489179733)
      ·
        refine ⟨1077557670694922935420075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 91951587899300090489179733 1077557670694922935420075)
        ·
          refine ⟨1616336506042384403130113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1077557670694922935420075 1616336506042384403130113)
          ·
            refine ⟨1212252379531788302347585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1616336506042384403130113 1212252379531788302347585)
            ·
              refine ⟨909189284648841226760689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1212252379531788302347585 909189284648841226760689)
              ·
                refine ⟨681891963486630920070517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 909189284648841226760689 681891963486630920070517)
                ·
                  refine ⟨63927371576871648756611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 681891963486630920070517 63927371576871648756611)
                  ·
                    rfl

theorem cell23_1120483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 2, 2, 5].length) (baseStart_1120483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1120483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1120483 prefixEnd_1120483 := by exact prefixLift 1120483
  have htrace : WordTrace (prefixWord ++ tailWord_1120483) baseStart_1120483 baseEnd_1120483 := by
    simpa [prefixWord, tailWord_1120483, baseEnd_1120483] using wordTrace_append hprefix tailTrace_1120483
  have hstable : (prefixWord ++ tailWord_1120483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120483).length < 2 ^ (prefixWord ++ tailWord_1120483).sum := by decide
  have hdescent : baseEnd_1120483 < baseStart_1120483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120492 : List Nat := [2, 2, 1, 1, 2, 3, 2, 3, 3, 4]
def baseStart_1120492 : Nat := 118140960795 + 1120492 * 2 ^ 59
def prefixEnd_1120492 : Nat := 4983230072969 + 3 ^ 40 * 1120492 * 2
def baseEnd_1120492 : Nat := 191783655172578434532319

theorem tailTrace_1120492 : CollatzResearch.WordTrace tailWord_1120492 prefixEnd_1120492 191783655172578434532319 := by
  unfold tailWord_1120492
  simp only [CollatzResearch.WordTrace]
  refine ⟨20433850328328161821689865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27245133771104215762253153 20433850328328161821689865)
  ·
    refine ⟨15325387746246121366267399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20433850328328161821689865 15325387746246121366267399)
    ·
      refine ⟨22988081619369182049401099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15325387746246121366267399 22988081619369182049401099)
      ·
        refine ⟨34482122429053773074101649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22988081619369182049401099 34482122429053773074101649)
        ·
          refine ⟨25861591821790329805576237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34482122429053773074101649 25861591821790329805576237)
          ·
            refine ⟨9698096933171373677091089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25861591821790329805576237 9698096933171373677091089)
            ·
              refine ⟨7273572699878530257818317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9698096933171373677091089 7273572699878530257818317)
              ·
                refine ⟨2727589762454448846681869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7273572699878530257818317 2727589762454448846681869)
                ·
                  refine ⟨1022846160920418317505701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2727589762454448846681869 1022846160920418317505701)
                  ·
                    refine ⟨191783655172578434532319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1022846160920418317505701 191783655172578434532319)
                    ·
                      rfl

theorem cell23_1120492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 4].length) (baseStart_1120492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1120492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1120492 prefixEnd_1120492 := by exact prefixLift 1120492
  have htrace : WordTrace (prefixWord ++ tailWord_1120492) baseStart_1120492 baseEnd_1120492 := by
    simpa [prefixWord, tailWord_1120492, baseEnd_1120492] using wordTrace_append hprefix tailTrace_1120492
  have hstable : (prefixWord ++ tailWord_1120492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120492).length < 2 ^ (prefixWord ++ tailWord_1120492).sum := by decide
  have hdescent : baseEnd_1120492 < baseStart_1120492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120516 : List Nat := [2, 3, 2, 2, 3, 2, 1, 1, 2, 1, 4]
def baseStart_1120516 : Nat := 118140960795 + 1120516 * 2 ^ 59
def prefixEnd_1120516 : Nat := 4983230072969 + 3 ^ 40 * 1120516 * 2
def baseEnd_1120516 : Nat := 575363289053443209696847

theorem tailTrace_1120516 : CollatzResearch.WordTrace tailWord_1120516 prefixEnd_1120516 575363289053443209696847 := by
  unfold tailWord_1120516
  simp only [CollatzResearch.WordTrace]
  refine ⟨20434288004284687871126701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27245717339046250494835601 20434288004284687871126701)
  ·
    refine ⟨7662858001606757951672513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20434288004284687871126701 7662858001606757951672513)
    ·
      refine ⟨5747143501205068463754385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7662858001606757951672513 5747143501205068463754385)
      ·
        refine ⟨4310357625903801347815789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5747143501205068463754385 4310357625903801347815789)
        ·
          refine ⟨1616384109713925505430921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4310357625903801347815789 1616384109713925505430921)
          ·
            refine ⟨1212288082285444129073191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1616384109713925505430921 1212288082285444129073191)
            ·
              refine ⟨1818432123428166193609787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1212288082285444129073191 1818432123428166193609787)
              ·
                refine ⟨2727648185142249290414681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1818432123428166193609787 2727648185142249290414681)
                ·
                  refine ⟨2045736138856686967811011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2727648185142249290414681 2045736138856686967811011)
                  ·
                    refine ⟨3068604208285030451716517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2045736138856686967811011 3068604208285030451716517)
                    ·
                      refine ⟨575363289053443209696847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3068604208285030451716517 575363289053443209696847)
                      ·
                        rfl

theorem cell23_1120516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_1120516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1120516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1120516 prefixEnd_1120516 := by exact prefixLift 1120516
  have htrace : WordTrace (prefixWord ++ tailWord_1120516) baseStart_1120516 baseEnd_1120516 := by
    simpa [prefixWord, tailWord_1120516, baseEnd_1120516] using wordTrace_append hprefix tailTrace_1120516
  have hstable : (prefixWord ++ tailWord_1120516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120516).length < 2 ^ (prefixWord ++ tailWord_1120516).sum := by decide
  have hdescent : baseEnd_1120516 < baseStart_1120516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120526 : List Nat := [4, 1, 1, 2, 1, 2, 4, 3, 1, 4]
def baseStart_1120526 : Nat := 118140960795 + 1120526 * 2 ^ 59
def prefixEnd_1120526 : Nat := 4983230072969 + 3 ^ 40 * 1120526 * 2
def baseEnd_1120526 : Nat := 191789474619996056857267

theorem tailTrace_1120526 : CollatzResearch.WordTrace tailWord_1120526 prefixEnd_1120526 191789474619996056857267 := by
  unfold tailWord_1120526
  simp only [CollatzResearch.WordTrace]
  refine ⟨5108617592316643431264679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27245960492355431633411621 5108617592316643431264679)
  ·
    refine ⟨7662926388474965146897019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5108617592316643431264679 7662926388474965146897019)
    ·
      refine ⟨11494389582712447720345529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7662926388474965146897019 11494389582712447720345529)
      ·
        refine ⟨8620792187034335790259147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11494389582712447720345529 8620792187034335790259147)
        ·
          refine ⟨12931188280551503685388721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8620792187034335790259147 12931188280551503685388721)
          ·
            refine ⟨9698391210413627764041541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12931188280551503685388721 9698391210413627764041541)
            ·
              refine ⟨1818448351952555205757789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9698391210413627764041541 1818448351952555205757789)
              ·
                refine ⟨681918131982208202159171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1818448351952555205757789 681918131982208202159171)
                ·
                  refine ⟨1022877197973312303238757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 681918131982208202159171 1022877197973312303238757)
                  ·
                    refine ⟨191789474619996056857267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1022877197973312303238757 191789474619996056857267)
                    ·
                      rfl

theorem cell23_1120526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 3, 1, 4].length) (baseStart_1120526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1120526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1120526 prefixEnd_1120526 := by exact prefixLift 1120526
  have htrace : WordTrace (prefixWord ++ tailWord_1120526) baseStart_1120526 baseEnd_1120526 := by
    simpa [prefixWord, tailWord_1120526, baseEnd_1120526] using wordTrace_append hprefix tailTrace_1120526
  have hstable : (prefixWord ++ tailWord_1120526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120526).length < 2 ^ (prefixWord ++ tailWord_1120526).sum := by decide
  have hdescent : baseEnd_1120526 < baseStart_1120526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120569 : List Nat := [1, 2, 1, 6, 1, 1, 1, 4, 1, 5]
def baseStart_1120569 : Nat := 118140960795 + 1120569 * 2 ^ 59
def prefixEnd_1120569 : Nat := 4983230072969 + 3 ^ 40 * 1120569 * 2
def baseEnd_1120569 : Nat := 191796834509377167444701

theorem tailTrace_1120569 : CollatzResearch.WordTrace tailWord_1120569 prefixEnd_1120569 191796834509377167444701 := by
  unfold tailWord_1120569
  simp only [CollatzResearch.WordTrace]
  refine ⟨40870509077377365793932761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27247006051584910529288507 40870509077377365793932761)
  ·
    refine ⟨30652881808033024345449571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40870509077377365793932761 30652881808033024345449571)
    ·
      refine ⟨45979322712049536518174357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30652881808033024345449571 45979322712049536518174357)
      ·
        refine ⟨2155280752127322024289423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 45979322712049536518174357 2155280752127322024289423)
        ·
          refine ⟨3232921128190983036434135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2155280752127322024289423 3232921128190983036434135)
          ·
            refine ⟨4849381692286474554651203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3232921128190983036434135 4849381692286474554651203)
            ·
              refine ⟨7274072538429711831976805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4849381692286474554651203 7274072538429711831976805)
              ·
                refine ⟨1363888600955570968495651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7274072538429711831976805 1363888600955570968495651)
                ·
                  refine ⟨2045832901433356452743477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1363888600955570968495651 2045832901433356452743477)
                  ·
                    refine ⟨191796834509377167444701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2045832901433356452743477 191796834509377167444701)
                    ·
                      rfl

theorem cell23_1120569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 4, 1, 5].length) (baseStart_1120569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1120569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1120569 prefixEnd_1120569 := by exact prefixLift 1120569
  have htrace : WordTrace (prefixWord ++ tailWord_1120569) baseStart_1120569 baseEnd_1120569 := by
    simpa [prefixWord, tailWord_1120569, baseEnd_1120569] using wordTrace_append hprefix tailTrace_1120569
  have hstable : (prefixWord ++ tailWord_1120569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120569).length < 2 ^ (prefixWord ++ tailWord_1120569).sum := by decide
  have hdescent : baseEnd_1120569 < baseStart_1120569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120592 : List Nat := [2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 5]
def baseStart_1120592 : Nat := 118140960795 + 1120592 * 2 ^ 59
def prefixEnd_1120592 : Nat := 4983230072969 + 3 ^ 40 * 1120592 * 2
def baseEnd_1120592 : Nat := 575402313583184912346497

theorem tailTrace_1120592 : CollatzResearch.WordTrace tailWord_1120592 prefixEnd_1120592 575402313583184912346497 := by
  unfold tailWord_1120592
  simp only [CollatzResearch.WordTrace]
  refine ⟨20435673978147020361010015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27247565304196027148013353 20435673978147020361010015)
  ·
    refine ⟨30653510967220530541515023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20435673978147020361010015 30653510967220530541515023)
    ·
      refine ⟨45980266450830795812272535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30653510967220530541515023 45980266450830795812272535)
      ·
        refine ⟨68970399676246193718408803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45980266450830795812272535 68970399676246193718408803)
        ·
          refine ⟨103455599514369290577613205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68970399676246193718408803 103455599514369290577613205)
          ·
            refine ⟨4849481227236060495825619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 103455599514369290577613205 4849481227236060495825619)
            ·
              refine ⟨7274221840854090743738429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4849481227236060495825619 7274221840854090743738429)
              ·
                refine ⟨2727833190320284028901911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7274221840854090743738429 2727833190320284028901911)
                ·
                  refine ⟨4091749785480426043352867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2727833190320284028901911 4091749785480426043352867)
                  ·
                    refine ⟨6137624678220639065029301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4091749785480426043352867 6137624678220639065029301)
                    ·
                      refine ⟨575402313583184912346497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6137624678220639065029301 575402313583184912346497)
                      ·
                        rfl

theorem cell23_1120592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 5].length) (baseStart_1120592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1120592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1120592 prefixEnd_1120592 := by exact prefixLift 1120592
  have htrace : WordTrace (prefixWord ++ tailWord_1120592) baseStart_1120592 baseEnd_1120592 := by
    simpa [prefixWord, tailWord_1120592, baseEnd_1120592] using wordTrace_append hprefix tailTrace_1120592
  have hstable : (prefixWord ++ tailWord_1120592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120592).length < 2 ^ (prefixWord ++ tailWord_1120592).sum := by decide
  have hdescent : baseEnd_1120592 < baseStart_1120592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120599 : List Nat := [1, 1, 3, 2, 3, 1, 2, 4, 2, 4]
def baseStart_1120599 : Nat := 118140960795 + 1120599 * 2 ^ 59
def prefixEnd_1120599 : Nat := 4983230072969 + 3 ^ 40 * 1120599 * 2
def baseEnd_1120599 : Nat := 191801969315922128319655

theorem tailTrace_1120599 : CollatzResearch.WordTrace tailWord_1120599 prefixEnd_1120599 191801969315922128319655 := by
  unfold tailWord_1120599
  simp only [CollatzResearch.WordTrace]
  refine ⟨40871603267268680917524851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27247735511512453945016567 40871603267268680917524851)
  ·
    refine ⟨61307404900903021376287277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40871603267268680917524851 61307404900903021376287277)
    ·
      refine ⟨22990276837838633016107729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61307404900903021376287277 22990276837838633016107729)
      ·
        refine ⟨17242707628378974762080797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22990276837838633016107729 17242707628378974762080797)
        ·
          refine ⟨6466015360642115535780299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17242707628378974762080797 6466015360642115535780299)
          ·
            refine ⟨9699023040963173303670449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6466015360642115535780299 9699023040963173303670449)
            ·
              refine ⟨7274267280722379977752837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9699023040963173303670449 7274267280722379977752837)
              ·
                refine ⟨1363925115135446245828657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7274267280722379977752837 1363925115135446245828657)
                ·
                  refine ⟨1022943836351584684371493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1363925115135446245828657 1022943836351584684371493)
                  ·
                    refine ⟨191801969315922128319655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1022943836351584684371493 191801969315922128319655)
                    ·
                      rfl

theorem cell23_1120599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 4, 2, 4].length) (baseStart_1120599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1120599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1120599 prefixEnd_1120599 := by exact prefixLift 1120599
  have htrace : WordTrace (prefixWord ++ tailWord_1120599) baseStart_1120599 baseEnd_1120599 := by
    simpa [prefixWord, tailWord_1120599, baseEnd_1120599] using wordTrace_append hprefix tailTrace_1120599
  have hstable : (prefixWord ++ tailWord_1120599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120599).length < 2 ^ (prefixWord ++ tailWord_1120599).sum := by decide
  have hdescent : baseEnd_1120599 < baseStart_1120599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120612 : List Nat := [2, 3, 1, 1, 3, 1, 4, 8]
def baseStart_1120612 : Nat := 118140960795 + 1120612 * 2 ^ 59
def prefixEnd_1120612 : Nat := 4983230072969 + 3 ^ 40 * 1120612 * 2
def baseEnd_1120612 : Nat := 21311577155417586448015

theorem tailTrace_1120612 : CollatzResearch.WordTrace tailWord_1120612 prefixEnd_1120612 21311577155417586448015 := by
  unfold tailWord_1120612
  simp only [CollatzResearch.WordTrace]
  refine ⟨20436038708110792068874045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27248051610814389425165393 20436038708110792068874045)
  ·
    refine ⟨7663514515541547025827767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20436038708110792068874045 7663514515541547025827767)
    ·
      refine ⟨11495271773312320538741651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7663514515541547025827767 11495271773312320538741651)
      ·
        refine ⟨17242907659968480808112477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11495271773312320538741651 17242907659968480808112477)
        ·
          refine ⟨6466090372488180303042179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17242907659968480808112477 6466090372488180303042179)
          ·
            refine ⟨9699135558732270454563269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6466090372488180303042179 9699135558732270454563269)
            ·
              refine ⟨1818587917262300710230613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9699135558732270454563269 1818587917262300710230613)
              ·
                refine ⟨21311577155417586448015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1818587917262300710230613 21311577155417586448015)
                ·
                  rfl

theorem cell23_1120612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 8].length) (baseStart_1120612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1120612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1120612 prefixEnd_1120612 := by exact prefixLift 1120612
  have htrace : WordTrace (prefixWord ++ tailWord_1120612) baseStart_1120612 baseEnd_1120612 := by
    simpa [prefixWord, tailWord_1120612, baseEnd_1120612] using wordTrace_append hprefix tailTrace_1120612
  have hstable : (prefixWord ++ tailWord_1120612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120612).length < 2 ^ (prefixWord ++ tailWord_1120612).sum := by decide
  have hdescent : baseEnd_1120612 < baseStart_1120612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120616 : List Nat := [2, 1, 4, 2, 2, 2, 1, 3, 2, 4]
def baseStart_1120616 : Nat := 118140960795 + 1120616 * 2 ^ 59
def prefixEnd_1120616 : Nat := 4983230072969 + 3 ^ 40 * 1120616 * 2
def baseEnd_1120616 : Nat := 191804879039630939482129

theorem tailTrace_1120616 : CollatzResearch.WordTrace tailWord_1120616 prefixEnd_1120616 191804879039630939482129 := by
  unfold tailWord_1120616
  simp only [CollatzResearch.WordTrace]
  refine ⟨20436111654103546410446851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27248148872138061880595801 20436111654103546410446851)
  ·
    refine ⟨30654167481155319615670277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20436111654103546410446851 30654167481155319615670277)
    ·
      refine ⟨5747656402716622427938177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30654167481155319615670277 5747656402716622427938177)
      ·
        refine ⟨4310742302037466820953633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5747656402716622427938177 4310742302037466820953633)
        ·
          refine ⟨3233056726528100115715225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4310742302037466820953633 3233056726528100115715225)
          ·
            refine ⟨2424792544896075086786419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3233056726528100115715225 2424792544896075086786419)
            ·
              refine ⟨3637188817344112630179629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2424792544896075086786419 3637188817344112630179629)
              ·
                refine ⟨1363945806504042236317361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3637188817344112630179629 1363945806504042236317361)
                ·
                  refine ⟨1022959354878031677238021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1363945806504042236317361 1022959354878031677238021)
                  ·
                    refine ⟨191804879039630939482129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1022959354878031677238021 191804879039630939482129)
                    ·
                      rfl

theorem cell23_1120616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 3, 2, 4].length) (baseStart_1120616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1120616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1120616 prefixEnd_1120616 := by exact prefixLift 1120616
  have htrace : WordTrace (prefixWord ++ tailWord_1120616) baseStart_1120616 baseEnd_1120616 := by
    simpa [prefixWord, tailWord_1120616, baseEnd_1120616] using wordTrace_append hprefix tailTrace_1120616
  have hstable : (prefixWord ++ tailWord_1120616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120616).length < 2 ^ (prefixWord ++ tailWord_1120616).sum := by decide
  have hdescent : baseEnd_1120616 < baseStart_1120616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120626 : List Nat := [3, 2, 1, 2, 1, 3, 3, 2, 1, 2, 3]
def baseStart_1120626 : Nat := 118140960795 + 1120626 * 2 ^ 59
def prefixEnd_1120626 : Nat := 4983230072969 + 3 ^ 40 * 1120626 * 2
def baseEnd_1120626 : Nat := 575419771925437779321341

theorem tailTrace_1120626 : CollatzResearch.WordTrace tailWord_1120626 prefixEnd_1120626 575419771925437779321341 := by
  unfold tailWord_1120626
  simp only [CollatzResearch.WordTrace]
  refine ⟨10218147009542716132189433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27248392025447243019171821 10218147009542716132189433)
  ·
    refine ⟨7663610257157037099142075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10218147009542716132189433 7663610257157037099142075)
    ·
      refine ⟨11495415385735555648713113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7663610257157037099142075 11495415385735555648713113)
      ·
        refine ⟨8621561539301666736534835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11495415385735555648713113 8621561539301666736534835)
        ·
          refine ⟨12932342308952500104802253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8621561539301666736534835 12932342308952500104802253)
          ·
            refine ⟨4849628365857187539300845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12932342308952500104802253 4849628365857187539300845)
            ·
              refine ⟨1818610637196445327237817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4849628365857187539300845 1818610637196445327237817)
              ·
                refine ⟨1363957977897333995428363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1818610637196445327237817 1363957977897333995428363)
                ·
                  refine ⟨2045936966846000993142545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1363957977897333995428363 2045936966846000993142545)
                  ·
                    refine ⟨1534452725134500744856909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2045936966846000993142545 1534452725134500744856909)
                    ·
                      refine ⟨575419771925437779321341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1534452725134500744856909 575419771925437779321341)
                      ·
                        rfl

theorem cell23_1120626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 2, 1, 2, 3].length) (baseStart_1120626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1120626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1120626 prefixEnd_1120626 := by exact prefixLift 1120626
  have htrace : WordTrace (prefixWord ++ tailWord_1120626) baseStart_1120626 baseEnd_1120626 := by
    simpa [prefixWord, tailWord_1120626, baseEnd_1120626] using wordTrace_append hprefix tailTrace_1120626
  have hstable : (prefixWord ++ tailWord_1120626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120626).length < 2 ^ (prefixWord ++ tailWord_1120626).sum := by decide
  have hdescent : baseEnd_1120626 < baseStart_1120626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120643 : List Nat := [1, 1, 1, 3, 6, 1, 3, 1, 1, 2, 3]
def baseStart_1120643 : Nat := 118140960795 + 1120643 * 2 ^ 59
def prefixEnd_1120643 : Nat := 4983230072969 + 3 ^ 40 * 1120643 * 2
def baseEnd_1120643 : Nat := 575428501096564212808763

theorem tailTrace_1120643 : CollatzResearch.WordTrace tailWord_1120643 prefixEnd_1120643 575428501096564212808763 := by
  unfold tailWord_1120643
  simp only [CollatzResearch.WordTrace]
  refine ⟨40873208079109276432126583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27248805386072850954751055 40873208079109276432126583)
  ·
    refine ⟨61309812118663914648189875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40873208079109276432126583 61309812118663914648189875)
    ·
      refine ⟨91964718177995871972284813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61309812118663914648189875 91964718177995871972284813)
      ·
        refine ⟨34486769316748451989606805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91964718177995871972284813 34486769316748451989606805)
        ·
          refine ⟨1616567311722583687012819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 34486769316748451989606805 1616567311722583687012819)
          ·
            refine ⟨2424850967583875530519229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1616567311722583687012819 2424850967583875530519229)
            ·
              refine ⟨909319112843953323944711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2424850967583875530519229 909319112843953323944711)
              ·
                refine ⟨1363978669265929985917067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 909319112843953323944711 1363978669265929985917067)
                ·
                  refine ⟨2045968003898894978875601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1363978669265929985917067 2045968003898894978875601)
                  ·
                    refine ⟨1534476002924171234156701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2045968003898894978875601 1534476002924171234156701)
                    ·
                      refine ⟨575428501096564212808763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1534476002924171234156701 575428501096564212808763)
                      ·
                        rfl

theorem cell23_1120643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 3, 1, 1, 2, 3].length) (baseStart_1120643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1120643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1120643 prefixEnd_1120643 := by exact prefixLift 1120643
  have htrace : WordTrace (prefixWord ++ tailWord_1120643) baseStart_1120643 baseEnd_1120643 := by
    simpa [prefixWord, tailWord_1120643, baseEnd_1120643] using wordTrace_append hprefix tailTrace_1120643
  have hstable : (prefixWord ++ tailWord_1120643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120643).length < 2 ^ (prefixWord ++ tailWord_1120643).sum := by decide
  have hdescent : baseEnd_1120643 < baseStart_1120643 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120666 : List Nat := [3, 1, 1, 4, 1, 2, 1, 2, 3, 3, 2]
def baseStart_1120666 : Nat := 118140960795 + 1120666 * 2 ^ 59
def prefixEnd_1120666 : Nat := 4983230072969 + 3 ^ 40 * 1120666 * 2
def baseEnd_1120666 : Nat := 575440311151617622821157

theorem tailTrace_1120666 : CollatzResearch.WordTrace tailWord_1120666 prefixEnd_1120666 575440311151617622821157 := by
  unfold tailWord_1120666
  simp only [CollatzResearch.WordTrace]
  refine ⟨10218511739506487840053463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27249364638683967573475901 10218511739506487840053463)
  ·
    refine ⟨15327767609259731760080195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10218511739506487840053463 15327767609259731760080195)
    ·
      refine ⟨22991651413889597640120293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15327767609259731760080195 22991651413889597640120293)
      ·
        refine ⟨4310934640104299557522555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22991651413889597640120293 4310934640104299557522555)
        ·
          refine ⟨6466401960156449336283833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4310934640104299557522555 6466401960156449336283833)
          ·
            refine ⟨4849801470117337002212875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6466401960156449336283833 4849801470117337002212875)
            ·
              refine ⟨7274702205176005503319313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4849801470117337002212875 7274702205176005503319313)
              ·
                refine ⟨5456026653882004127489485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7274702205176005503319313 5456026653882004127489485)
                ·
                  refine ⟨2046009995205751547808557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5456026653882004127489485 2046009995205751547808557)
                  ·
                    refine ⟨767253748202156830428209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2046009995205751547808557 767253748202156830428209)
                    ·
                      refine ⟨575440311151617622821157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 767253748202156830428209 575440311151617622821157)
                      ·
                        rfl

theorem cell23_1120666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 3, 3, 2].length) (baseStart_1120666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1120666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1120666 prefixEnd_1120666 := by exact prefixLift 1120666
  have htrace : WordTrace (prefixWord ++ tailWord_1120666) baseStart_1120666 baseEnd_1120666 := by
    simpa [prefixWord, tailWord_1120666, baseEnd_1120666] using wordTrace_append hprefix tailTrace_1120666
  have hstable : (prefixWord ++ tailWord_1120666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120666).length < 2 ^ (prefixWord ++ tailWord_1120666).sum := by decide
  have hdescent : baseEnd_1120666 < baseStart_1120666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120672 : List Nat := [2, 1, 1, 4, 1, 3, 1, 1, 1, 8]
def baseStart_1120672 : Nat := 118140960795 + 1120672 * 2 ^ 59
def prefixEnd_1120672 : Nat := 4983230072969 + 3 ^ 40 * 1120672 * 2
def baseEnd_1120672 : Nat := 191814464011848199782043

theorem tailTrace_1120672 : CollatzResearch.WordTrace tailWord_1120672 prefixEnd_1120672 191814464011848199782043 := by
  unfold tailWord_1120672
  simp only [CollatzResearch.WordTrace]
  refine ⟨20437132898002107192466135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27249510530669476256621513 20437132898002107192466135)
  ·
    refine ⟨30655699347003160788699203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20437132898002107192466135 30655699347003160788699203)
    ·
      refine ⟨45983549020504741183048805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30655699347003160788699203 45983549020504741183048805)
      ·
        refine ⟨8621915441344638971821651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45983549020504741183048805 8621915441344638971821651)
        ·
          refine ⟨12932873162016958457732477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8621915441344638971821651 12932873162016958457732477)
          ·
            refine ⟨4849827435756359421649679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12932873162016958457732477 4849827435756359421649679)
            ·
              refine ⟨7274741153634539132474519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4849827435756359421649679 7274741153634539132474519)
              ·
                refine ⟨10912111730451808698711779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7274741153634539132474519 10912111730451808698711779)
                ·
                  refine ⟨16368167595677713048067669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10912111730451808698711779 16368167595677713048067669)
                  ·
                    refine ⟨191814464011848199782043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 16368167595677713048067669 191814464011848199782043)
                    ·
                      rfl

theorem cell23_1120672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 1, 8].length) (baseStart_1120672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1120672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1120672 prefixEnd_1120672 := by exact prefixLift 1120672
  have htrace : WordTrace (prefixWord ++ tailWord_1120672) baseStart_1120672 baseEnd_1120672 := by
    simpa [prefixWord, tailWord_1120672, baseEnd_1120672] using wordTrace_append hprefix tailTrace_1120672
  have hstable : (prefixWord ++ tailWord_1120672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120672).length < 2 ^ (prefixWord ++ tailWord_1120672).sum := by decide
  have hdescent : baseEnd_1120672 < baseStart_1120672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120673 : List Nat := [1, 2, 3, 5, 1, 1, 2, 1, 1, 3, 3]
def baseStart_1120673 : Nat := 118140960795 + 1120673 * 2 ^ 59
def prefixEnd_1120673 : Nat := 4983230072969 + 3 ^ 40 * 1120673 * 2
def baseEnd_1120673 : Nat := 575443905516199095433625

theorem tailTrace_1120673 : CollatzResearch.WordTrace tailWord_1120673 prefixEnd_1120673 575443905516199095433625 := by
  unfold tailWord_1120673
  simp only [CollatzResearch.WordTrace]
  refine ⟨40874302269000591555718673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27249534846000394370479115 40874302269000591555718673)
  ·
    refine ⟨30655726701750443666789005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40874302269000591555718673 30655726701750443666789005)
    ·
      refine ⟨11495897513156416375045877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30655726701750443666789005 11495897513156416375045877)
      ·
        refine ⟨1077740391858414035160551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11495897513156416375045877 1077740391858414035160551)
        ·
          refine ⟨1616610587787621052740827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1077740391858414035160551 1616610587787621052740827)
          ·
            refine ⟨2424915881681431579111241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1616610587787621052740827 2424915881681431579111241)
            ·
              refine ⟨1818686911261073684333431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2424915881681431579111241 1818686911261073684333431)
              ·
                refine ⟨2728030366891610526500147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1818686911261073684333431 2728030366891610526500147)
                ·
                  refine ⟨4092045550337415789750221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2728030366891610526500147 4092045550337415789750221)
                  ·
                    refine ⟨1534517081376530921156333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4092045550337415789750221 1534517081376530921156333)
                    ·
                      refine ⟨575443905516199095433625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1534517081376530921156333 575443905516199095433625)
                      ·
                        rfl

theorem cell23_1120673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_1120673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1120673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1120673 prefixEnd_1120673 := by exact prefixLift 1120673
  have htrace : WordTrace (prefixWord ++ tailWord_1120673) baseStart_1120673 baseEnd_1120673 := by
    simpa [prefixWord, tailWord_1120673, baseEnd_1120673] using wordTrace_append hprefix tailTrace_1120673
  have hstable : (prefixWord ++ tailWord_1120673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120673).length < 2 ^ (prefixWord ++ tailWord_1120673).sum := by decide
  have hdescent : baseEnd_1120673 < baseStart_1120673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120696 : List Nat := [2, 1, 2, 1, 2, 2, 1, 4, 4, 2, 2]
def baseStart_1120696 : Nat := 118140960795 + 1120696 * 2 ^ 59
def prefixEnd_1120696 : Nat := 4983230072969 + 3 ^ 40 * 1120696 * 2
def baseEnd_1120696 : Nat := 575455715571252505446019

theorem tailTrace_1120696 : CollatzResearch.WordTrace tailWord_1120696 prefixEnd_1120696 575455715571252505446019 := by
  unfold tailWord_1120696
  simp only [CollatzResearch.WordTrace]
  refine ⟨20437570573958633241902971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27250094098611510989203961 20437570573958633241902971)
  ·
    refine ⟨30656355860937949862854457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20437570573958633241902971 30656355860937949862854457)
    ·
      refine ⟨22992266895703462397140843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30656355860937949862854457 22992266895703462397140843)
      ·
        refine ⟨34488400343555193595711265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22992266895703462397140843 34488400343555193595711265)
        ·
          refine ⟨25866300257666395196783449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34488400343555193595711265 25866300257666395196783449)
          ·
            refine ⟨19399725193249796397587587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25866300257666395196783449 19399725193249796397587587)
            ·
              refine ⟨29099587789874694596381381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19399725193249796397587587 29099587789874694596381381)
              ·
                refine ⟨5456172710601505236821509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29099587789874694596381381 5456172710601505236821509)
                ·
                  refine ⟨1023032383237782231904033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5456172710601505236821509 1023032383237782231904033)
                  ·
                    refine ⟨767274287428336673928025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1023032383237782231904033 767274287428336673928025)
                    ·
                      refine ⟨575455715571252505446019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 767274287428336673928025 575455715571252505446019)
                      ·
                        rfl

theorem cell23_1120696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 4, 2, 2].length) (baseStart_1120696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1120696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1120696 prefixEnd_1120696 := by exact prefixLift 1120696
  have htrace : WordTrace (prefixWord ++ tailWord_1120696) baseStart_1120696 baseEnd_1120696 := by
    simpa [prefixWord, tailWord_1120696, baseEnd_1120696] using wordTrace_append hprefix tailTrace_1120696
  have hstable : (prefixWord ++ tailWord_1120696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120696).length < 2 ^ (prefixWord ++ tailWord_1120696).sum := by decide
  have hdescent : baseEnd_1120696 < baseStart_1120696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120700 : List Nat := [2, 2, 2, 4, 1, 1, 4, 1, 1, 3, 2]
def baseStart_1120700 : Nat := 118140960795 + 1120700 * 2 ^ 59
def prefixEnd_1120700 : Nat := 4983230072969 + 3 ^ 40 * 1120700 * 2
def baseEnd_1120700 : Nat := 575457769493870489796001

theorem tailTrace_1120700 : CollatzResearch.WordTrace tailWord_1120700 prefixEnd_1120700 575457769493870489796001 := by
  unfold tailWord_1120700
  simp only [CollatzResearch.WordTrace]
  refine ⟨20437643519951387583475777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27250191359935183444634369 20437643519951387583475777)
  ·
    refine ⟨15328232639963540687606833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20437643519951387583475777 15328232639963540687606833)
    ·
      refine ⟨11496174479972655515705125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15328232639963540687606833 11496174479972655515705125)
      ·
        refine ⟨2155532714994872909194711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11496174479972655515705125 2155532714994872909194711)
        ·
          refine ⟨3233299072492309363792067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2155532714994872909194711 3233299072492309363792067)
          ·
            refine ⟨4849948608738464045688101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3233299072492309363792067 4849948608738464045688101)
            ·
              refine ⟨909365364138462008566519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4849948608738464045688101 909365364138462008566519)
              ·
                refine ⟨1364048046207693012849779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 909365364138462008566519 1364048046207693012849779)
                ·
                  refine ⟨2046072069311539519274669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1364048046207693012849779 2046072069311539519274669)
                  ·
                    refine ⟨767277025991827319728001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2046072069311539519274669 767277025991827319728001)
                    ·
                      refine ⟨575457769493870489796001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 767277025991827319728001 575457769493870489796001)
                      ·
                        rfl

theorem cell23_1120700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_1120700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1120700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1120700 prefixEnd_1120700 := by exact prefixLift 1120700
  have htrace : WordTrace (prefixWord ++ tailWord_1120700) baseStart_1120700 baseEnd_1120700 := by
    simpa [prefixWord, tailWord_1120700, baseEnd_1120700] using wordTrace_append hprefix tailTrace_1120700
  have hstable : (prefixWord ++ tailWord_1120700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120700).length < 2 ^ (prefixWord ++ tailWord_1120700).sum := by decide
  have hdescent : baseEnd_1120700 < baseStart_1120700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120713 : List Nat := [1, 2, 1, 1, 2, 1, 7, 2, 2, 2, 2]
def baseStart_1120713 : Nat := 118140960795 + 1120713 * 2 ^ 59
def prefixEnd_1120713 : Nat := 4983230072969 + 3 ^ 40 * 1120713 * 2
def baseEnd_1120713 : Nat := 575464444742378938933441

theorem tailTrace_1120713 : CollatzResearch.WordTrace tailWord_1120713 prefixEnd_1120713 575464444742378938933441 := by
  unfold tailWord_1120713
  simp only [CollatzResearch.WordTrace]
  refine ⟨40875761188855678387174793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27250507459237118924783195 40875761188855678387174793)
  ·
    refine ⟨30656820891641758790381095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40875761188855678387174793 30656820891641758790381095)
    ·
      refine ⟨45985231337462638185571643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30656820891641758790381095 45985231337462638185571643)
      ·
        refine ⟨68977847006193957278357465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45985231337462638185571643 68977847006193957278357465)
        ·
          refine ⟨51733385254645467958768099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68977847006193957278357465 51733385254645467958768099)
          ·
            refine ⟨77600077881968201938152149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51733385254645467958768099 77600077881968201938152149)
            ·
              refine ⟨1818751825358629732925441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 77600077881968201938152149 1818751825358629732925441)
              ·
                refine ⟨1364063869018972299694081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1818751825358629732925441 1364063869018972299694081)
                ·
                  refine ⟨1023047901764229224770561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1364063869018972299694081 1023047901764229224770561)
                  ·
                    refine ⟨767285926323171918577921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1023047901764229224770561 767285926323171918577921)
                    ·
                      refine ⟨575464444742378938933441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 767285926323171918577921 575464444742378938933441)
                      ·
                        rfl

theorem cell23_1120713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 2, 2, 2, 2].length) (baseStart_1120713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1120713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1120713 prefixEnd_1120713 := by exact prefixLift 1120713
  have htrace : WordTrace (prefixWord ++ tailWord_1120713) baseStart_1120713 baseEnd_1120713 := by
    simpa [prefixWord, tailWord_1120713, baseEnd_1120713] using wordTrace_append hprefix tailTrace_1120713
  have hstable : (prefixWord ++ tailWord_1120713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120713).length < 2 ^ (prefixWord ++ tailWord_1120713).sum := by decide
  have hdescent : baseEnd_1120713 < baseStart_1120713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120726 : List Nat := [5, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4]
def baseStart_1120726 : Nat := 118140960795 + 1120726 * 2 ^ 59
def prefixEnd_1120726 : Nat := 4983230072969 + 3 ^ 40 * 1120726 * 2
def baseEnd_1120726 : Nat := 575471119990887388070881

theorem tailTrace_1120726 : CollatzResearch.WordTrace tailWord_1120726 prefixEnd_1120726 575471119990887388070881 := by
  unfold tailWord_1120726
  simp only [CollatzResearch.WordTrace]
  refine ⟨2554764708613036350462377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27250823558539054404932021 2554764708613036350462377)
  ·
    refine ⟨1916073531459777262846783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2554764708613036350462377 1916073531459777262846783)
    ·
      refine ⟨2874110297189665894270175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1916073531459777262846783 2874110297189665894270175)
      ·
        refine ⟨4311165445784498841405263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2874110297189665894270175 4311165445784498841405263)
        ·
          refine ⟨6466748168676748262107895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4311165445784498841405263 6466748168676748262107895)
          ·
            refine ⟨9700122253015122393161843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6466748168676748262107895 9700122253015122393161843)
            ·
              refine ⟨14550183379522683589742765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9700122253015122393161843 14550183379522683589742765)
              ·
                refine ⟨5456318767321006346153537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14550183379522683589742765 5456318767321006346153537)
                ·
                  refine ⟨4092239075490754759615153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5456318767321006346153537 4092239075490754759615153)
                  ·
                    refine ⟨3069179306618066069711365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4092239075490754759615153 3069179306618066069711365)
                    ·
                      refine ⟨575471119990887388070881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3069179306618066069711365 575471119990887388070881)
                      ·
                        rfl

theorem cell23_1120726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_1120726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1120726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1120726 prefixEnd_1120726 := by exact prefixLift 1120726
  have htrace : WordTrace (prefixWord ++ tailWord_1120726) baseStart_1120726 baseEnd_1120726 := by
    simpa [prefixWord, tailWord_1120726, baseEnd_1120726] using wordTrace_append hprefix tailTrace_1120726
  have hstable : (prefixWord ++ tailWord_1120726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120726).length < 2 ^ (prefixWord ++ tailWord_1120726).sum := by decide
  have hdescent : baseEnd_1120726 < baseStart_1120726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120729 : List Nat := [1, 2, 1, 2, 4, 1, 1, 3, 2, 3, 3]
def baseStart_1120729 : Nat := 118140960795 + 1120729 * 2 ^ 59
def prefixEnd_1120729 : Nat := 4983230072969 + 3 ^ 40 * 1120729 * 2
def baseEnd_1120729 : Nat := 575472660432850876333367

theorem tailTrace_1120729 : CollatzResearch.WordTrace tailWord_1120729 prefixEnd_1120729 575472660432850876333367 := by
  unfold tailWord_1120729
  simp only [CollatzResearch.WordTrace]
  refine ⟨40876344756797713119757241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27250896504531808746504827 40876344756797713119757241)
  ·
    refine ⟨30657258567598284839817931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40876344756797713119757241 30657258567598284839817931)
    ·
      refine ⟨45985887851397427259726897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30657258567598284839817931 45985887851397427259726897)
      ·
        refine ⟨34489415888548070444795173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45985887851397427259726897 34489415888548070444795173)
        ·
          refine ⟨6466765479102763208399095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34489415888548070444795173 6466765479102763208399095)
          ·
            refine ⟨9700148218654144812598643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6466765479102763208399095 9700148218654144812598643)
            ·
              refine ⟨14550222327981217218897965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9700148218654144812598643 14550222327981217218897965)
              ·
                refine ⟨5456333372992956457086737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14550222327981217218897965 5456333372992956457086737)
                ·
                  refine ⟨4092250029744717342815053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5456333372992956457086737 4092250029744717342815053)
                  ·
                    refine ⟨1534593761154269003555645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4092250029744717342815053 1534593761154269003555645)
                    ·
                      refine ⟨575472660432850876333367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1534593761154269003555645 575472660432850876333367)
                      ·
                        rfl

theorem cell23_1120729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 2, 3, 3].length) (baseStart_1120729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1120729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1120729 prefixEnd_1120729 := by exact prefixLift 1120729
  have htrace : WordTrace (prefixWord ++ tailWord_1120729) baseStart_1120729 baseEnd_1120729 := by
    simpa [prefixWord, tailWord_1120729, baseEnd_1120729] using wordTrace_append hprefix tailTrace_1120729
  have hstable : (prefixWord ++ tailWord_1120729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120729).length < 2 ^ (prefixWord ++ tailWord_1120729).sum := by decide
  have hdescent : baseEnd_1120729 < baseStart_1120729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120730 : List Nat := [3, 1, 1, 2, 3, 1, 5, 1, 2, 2, 2]
def baseStart_1120730 : Nat := 118140960795 + 1120730 * 2 ^ 59
def prefixEnd_1120730 : Nat := 4983230072969 + 3 ^ 40 * 1120730 * 2
def baseEnd_1120730 : Nat := 575473173913505372420863

theorem tailTrace_1120730 : CollatzResearch.WordTrace tailWord_1120730 prefixEnd_1120730 575473173913505372420863 := by
  unfold tailWord_1120730
  simp only [CollatzResearch.WordTrace]
  refine ⟨10219095307448522572635911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27250920819862726860362429 10219095307448522572635911)
  ·
    refine ⟨15328642961172783858953867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10219095307448522572635911 15328642961172783858953867)
    ·
      refine ⟨22992964441759175788430801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15328642961172783858953867 22992964441759175788430801)
      ·
        refine ⟨17244723331319381841323101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22992964441759175788430801 17244723331319381841323101)
        ·
          refine ⟨6466771249244768190496163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17244723331319381841323101 6466771249244768190496163)
          ·
            refine ⟨9700156873867152285744245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6466771249244768190496163 9700156873867152285744245)
            ·
              refine ⟨909389706925045526788523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9700156873867152285744245 909389706925045526788523)
              ·
                refine ⟨1364084560387568290182785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 909389706925045526788523 1364084560387568290182785)
                ·
                  refine ⟨1023063420290676217637089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1364084560387568290182785 1023063420290676217637089)
                  ·
                    refine ⟨767297565218007163227817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1023063420290676217637089 767297565218007163227817)
                    ·
                      refine ⟨575473173913505372420863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 767297565218007163227817 575473173913505372420863)
                      ·
                        rfl

theorem cell23_1120730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 5, 1, 2, 2, 2].length) (baseStart_1120730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1120730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1120730 prefixEnd_1120730 := by exact prefixLift 1120730
  have htrace : WordTrace (prefixWord ++ tailWord_1120730) baseStart_1120730 baseEnd_1120730 := by
    simpa [prefixWord, tailWord_1120730, baseEnd_1120730] using wordTrace_append hprefix tailTrace_1120730
  have hstable : (prefixWord ++ tailWord_1120730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120730).length < 2 ^ (prefixWord ++ tailWord_1120730).sum := by decide
  have hdescent : baseEnd_1120730 < baseStart_1120730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120770 : List Nat := [3, 4, 1, 2, 3, 1, 1, 1, 7]
def baseStart_1120770 : Nat := 118140960795 + 1120770 * 2 ^ 59
def prefixEnd_1120770 : Nat := 4983230072969 + 3 ^ 40 * 1120770 * 2
def baseEnd_1120770 : Nat := 63943745904409468435631

theorem tailTrace_1120770 : CollatzResearch.WordTrace tailWord_1120770 prefixEnd_1120770 63943745904409468435631 := by
  unfold tailWord_1120770
  simp only [CollatzResearch.WordTrace]
  refine ⟨10219460037412294280499941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27251893433099451414666509 10219460037412294280499941)
  ·
    refine ⟨1916148757014805177593739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10219460037412294280499941 1916148757014805177593739)
    ·
      refine ⟨2874223135522207766390609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1916148757014805177593739 2874223135522207766390609)
      ·
        refine ⟨2155667351641655824792957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2874223135522207766390609 2155667351641655824792957)
        ·
          refine ⟨808375256865620934297359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2155667351641655824792957 808375256865620934297359)
          ·
            refine ⟨1212562885298431401446039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 808375256865620934297359 1212562885298431401446039)
            ·
              refine ⟨1818844327947647102169059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1212562885298431401446039 1818844327947647102169059)
              ·
                refine ⟨2728266491921470653253589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1818844327947647102169059 2728266491921470653253589)
                ·
                  refine ⟨63943745904409468435631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2728266491921470653253589 63943745904409468435631)
                  ·
                    rfl

theorem cell23_1120770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 1, 7].length) (baseStart_1120770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1120770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1120770 prefixEnd_1120770 := by exact prefixLift 1120770
  have htrace : WordTrace (prefixWord ++ tailWord_1120770) baseStart_1120770 baseEnd_1120770 := by
    simpa [prefixWord, tailWord_1120770, baseEnd_1120770] using wordTrace_append hprefix tailTrace_1120770
  have hstable : (prefixWord ++ tailWord_1120770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120770).length < 2 ^ (prefixWord ++ tailWord_1120770).sum := by decide
  have hdescent : baseEnd_1120770 < baseStart_1120770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120781 : List Nat := [1, 7, 1, 1, 1, 3, 2, 1, 2, 2, 2]
def baseStart_1120781 : Nat := 118140960795 + 1120781 * 2 ^ 59
def prefixEnd_1120781 : Nat := 4983230072969 + 3 ^ 40 * 1120781 * 2
def baseEnd_1120781 : Nat := 575499361426884672883129

theorem tailTrace_1120781 : CollatzResearch.WordTrace tailWord_1120781 prefixEnd_1120781 575499361426884672883129 := by
  unfold tailWord_1120781
  simp only [CollatzResearch.WordTrace]
  refine ⟨40878241352609326000650197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27252160901739550667100131 40878241352609326000650197)
  ·
    refine ⟨958083781701781078140239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 40878241352609326000650197 958083781701781078140239)
    ·
      refine ⟨1437125672552671617210359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 958083781701781078140239 1437125672552671617210359)
      ·
        refine ⟨2155688508829007425815539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1437125672552671617210359 2155688508829007425815539)
        ·
          refine ⟨3233532763243511138723309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2155688508829007425815539 3233532763243511138723309)
          ·
            refine ⟨1212574786216316677021241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3233532763243511138723309 1212574786216316677021241)
            ·
              refine ⟨909431089662237507765931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1212574786216316677021241 909431089662237507765931)
              ·
                refine ⟨1364146634493356261648897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 909431089662237507765931 1364146634493356261648897)
                ·
                  refine ⟨1023109975870017196236673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1364146634493356261648897 1023109975870017196236673)
                  ·
                    refine ⟨767332481902512897177505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1023109975870017196236673 767332481902512897177505)
                    ·
                      refine ⟨575499361426884672883129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 767332481902512897177505 575499361426884672883129)
                      ·
                        rfl

theorem cell23_1120781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_1120781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1120781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1120781 prefixEnd_1120781 := by exact prefixLift 1120781
  have htrace : WordTrace (prefixWord ++ tailWord_1120781) baseStart_1120781 baseEnd_1120781 := by
    simpa [prefixWord, tailWord_1120781, baseEnd_1120781] using wordTrace_append hprefix tailTrace_1120781
  have hstable : (prefixWord ++ tailWord_1120781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120781).length < 2 ^ (prefixWord ++ tailWord_1120781).sum := by decide
  have hdescent : baseEnd_1120781 < baseStart_1120781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120826 : List Nat := [3, 1, 1, 1, 3, 4, 2, 2, 6]
def baseStart_1120826 : Nat := 118140960795 + 1120826 * 2 ^ 59
def prefixEnd_1120826 : Nat := 4983230072969 + 3 ^ 40 * 1120826 * 2
def baseEnd_1120826 : Nat := 63946940895148555202269

theorem tailTrace_1120826 : CollatzResearch.WordTrace tailWord_1120826 prefixEnd_1120826 63946940895148555202269 := by
  unfold tailWord_1120826
  simp only [CollatzResearch.WordTrace]
  refine ⟨10219970659361574671509583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27253255091630865790692221 10219970659361574671509583)
  ·
    refine ⟨15329955989042362007264375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10219970659361574671509583 15329955989042362007264375)
    ·
      refine ⟨22994933983563543010896563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15329955989042362007264375 22994933983563543010896563)
      ·
        refine ⟨34492400975345314516344845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22994933983563543010896563 34492400975345314516344845)
        ·
          refine ⟨12934650365754492943629317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34492400975345314516344845 12934650365754492943629317)
          ·
            refine ⟨2425246943578967426930497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12934650365754492943629317 2425246943578967426930497)
            ·
              refine ⟨1818935207684225570197873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2425246943578967426930497 1818935207684225570197873)
              ·
                refine ⟨1364201405763169177648405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1818935207684225570197873 1364201405763169177648405)
                ·
                  refine ⟨63946940895148555202269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1364201405763169177648405 63946940895148555202269)
                  ·
                    rfl

theorem cell23_1120826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 2, 6].length) (baseStart_1120826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1120826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1120826 prefixEnd_1120826 := by exact prefixLift 1120826
  have htrace : WordTrace (prefixWord ++ tailWord_1120826) baseStart_1120826 baseEnd_1120826 := by
    simpa [prefixWord, tailWord_1120826, baseEnd_1120826] using wordTrace_append hprefix tailTrace_1120826
  have hstable : (prefixWord ++ tailWord_1120826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120826).length < 2 ^ (prefixWord ++ tailWord_1120826).sum := by decide
  have hdescent : baseEnd_1120826 < baseStart_1120826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120896 : List Nat := [2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 5]
def baseStart_1120896 : Nat := 118140960795 + 1120896 * 2 ^ 59
def prefixEnd_1120896 : Nat := 4983230072969 + 3 ^ 40 * 1120896 * 2
def baseEnd_1120896 : Nat := 575558411702151722945099

theorem tailTrace_1120896 : CollatzResearch.WordTrace tailWord_1120896 prefixEnd_1120896 575558411702151722945099 := by
  unfold tailWord_1120896
  simp only [CollatzResearch.WordTrace]
  refine ⟨20441217873596350320543271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27254957164795133760724361 20441217873596350320543271)
  ·
    refine ⟨30661826810394525480814907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20441217873596350320543271 30661826810394525480814907)
    ·
      refine ⟨45992740215591788221222361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30661826810394525480814907 45992740215591788221222361)
      ·
        refine ⟨34494555161693841165916771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45992740215591788221222361 34494555161693841165916771)
        ·
          refine ⟨51741832742540761748875157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34494555161693841165916771 51741832742540761748875157)
          ·
            refine ⟨2425398409806598206978523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 51741832742540761748875157 2425398409806598206978523)
            ·
              refine ⟨3638097614709897310467785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2425398409806598206978523 3638097614709897310467785)
              ·
                refine ⟨2728573211032422982850839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3638097614709897310467785 2728573211032422982850839)
                ·
                  refine ⟨4092859816548634474276259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2728573211032422982850839 4092859816548634474276259)
                  ·
                    refine ⟨6139289724822951711414389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4092859816548634474276259 6139289724822951711414389)
                    ·
                      refine ⟨575558411702151722945099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6139289724822951711414389 575558411702151722945099)
                      ·
                        rfl

theorem cell23_1120896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 5].length) (baseStart_1120896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1120896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1120896 prefixEnd_1120896 := by exact prefixLift 1120896
  have htrace : WordTrace (prefixWord ++ tailWord_1120896) baseStart_1120896 baseEnd_1120896 := by
    simpa [prefixWord, tailWord_1120896, baseEnd_1120896] using wordTrace_append hprefix tailTrace_1120896
  have hstable : (prefixWord ++ tailWord_1120896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120896).length < 2 ^ (prefixWord ++ tailWord_1120896).sum := by decide
  have hdescent : baseEnd_1120896 < baseStart_1120896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120910 : List Nat := [4, 1, 1, 3, 1, 1, 1, 4, 3, 2, 2]
def baseStart_1120910 : Nat := 118140960795 + 1120910 * 2 ^ 59
def prefixEnd_1120910 : Nat := 4983230072969 + 3 ^ 40 * 1120910 * 2
def baseEnd_1120910 : Nat := 575565600431314668170035

theorem tailTrace_1120910 : CollatzResearch.WordTrace tailWord_1120910 prefixEnd_1120910 575565600431314668170035 := by
  unfold tailWord_1120910
  simp only [CollatzResearch.WordTrace]
  refine ⟨5110368296142747629012023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27255297579427987354730789 5110368296142747629012023)
  ·
    refine ⟨7665552444214121443518035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5110368296142747629012023 7665552444214121443518035)
    ·
      refine ⟨11498328666321182165277053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7665552444214121443518035 11498328666321182165277053)
      ·
        refine ⟨4311873249870443311978895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11498328666321182165277053 4311873249870443311978895)
        ·
          refine ⟨6467809874805664967968343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4311873249870443311978895 6467809874805664967968343)
          ·
            refine ⟨9701714812208497451952515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6467809874805664967968343 9701714812208497451952515)
            ·
              refine ⟨14552572218312746177928773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9701714812208497451952515 14552572218312746177928773)
              ·
                refine ⟨2728607290933639908361645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14552572218312746177928773 2728607290933639908361645)
                ·
                  refine ⟨1023227734100114965635617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2728607290933639908361645 1023227734100114965635617)
                  ·
                    refine ⟨767420800575086224226713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1023227734100114965635617 767420800575086224226713)
                    ·
                      refine ⟨575565600431314668170035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 767420800575086224226713 575565600431314668170035)
                      ·
                        rfl

theorem cell23_1120910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 4, 3, 2, 2].length) (baseStart_1120910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1120910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1120910 prefixEnd_1120910 := by exact prefixLift 1120910
  have htrace : WordTrace (prefixWord ++ tailWord_1120910) baseStart_1120910 baseEnd_1120910 := by
    simpa [prefixWord, tailWord_1120910, baseEnd_1120910] using wordTrace_append hprefix tailTrace_1120910
  have hstable : (prefixWord ++ tailWord_1120910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120910).length < 2 ^ (prefixWord ++ tailWord_1120910).sum := by decide
  have hdescent : baseEnd_1120910 < baseStart_1120910 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120943 : List Nat := [1, 1, 2, 1, 2, 5, 2, 1, 4, 1, 3]
def baseStart_1120943 : Nat := 118140960795 + 1120943 * 2 ^ 59
def prefixEnd_1120943 : Nat := 4983230072969 + 3 ^ 40 * 1120943 * 2
def baseEnd_1120943 : Nat := 575582545292913039057383

theorem tailTrace_1120943 : CollatzResearch.WordTrace tailWord_1120943 prefixEnd_1120943 575582545292913039057383 := by
  unfold tailWord_1120943
  simp only [CollatzResearch.WordTrace]
  refine ⟨40884149978022427668047483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27256099985348285112031655 40884149978022427668047483)
  ·
    refine ⟨61326224967033641502071225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40884149978022427668047483 61326224967033641502071225)
    ·
      refine ⟨45994668725275231126553419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61326224967033641502071225 45994668725275231126553419)
      ·
        refine ⟨68992003087912846689830129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45994668725275231126553419 68992003087912846689830129)
        ·
          refine ⟨51744002315934635017372597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68992003087912846689830129 51744002315934635017372597)
          ·
            refine ⟨4851000217118872032878681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51744002315934635017372597 4851000217118872032878681)
            ·
              refine ⟨3638250162839154024659011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4851000217118872032878681 3638250162839154024659011)
              ·
                refine ⟨5457375244258731036988517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3638250162839154024659011 5457375244258731036988517)
                ·
                  refine ⟨1023257858298512069435347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5457375244258731036988517 1023257858298512069435347)
                  ·
                    refine ⟨1534886787447768104153021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1023257858298512069435347 1534886787447768104153021)
                    ·
                      refine ⟨575582545292913039057383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1534886787447768104153021 575582545292913039057383)
                      ·
                        rfl

theorem cell23_1120943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 4, 1, 3].length) (baseStart_1120943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1120943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1120943 prefixEnd_1120943 := by exact prefixLift 1120943
  have htrace : WordTrace (prefixWord ++ tailWord_1120943) baseStart_1120943 baseEnd_1120943 := by
    simpa [prefixWord, tailWord_1120943, baseEnd_1120943] using wordTrace_append hprefix tailTrace_1120943
  have hstable : (prefixWord ++ tailWord_1120943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120943).length < 2 ^ (prefixWord ++ tailWord_1120943).sum := by decide
  have hdescent : baseEnd_1120943 < baseStart_1120943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120950 : List Nat := [5, 1, 3, 1, 2, 1, 2, 8]
def baseStart_1120950 : Nat := 118140960795 + 1120950 * 2 ^ 59
def prefixEnd_1120950 : Nat := 4983230072969 + 3 ^ 40 * 1120950 * 2
def baseEnd_1120950 : Nat := 21318005172499796728513

theorem tailTrace_1120950 : CollatzResearch.WordTrace tailWord_1120950 prefixEnd_1120950 21318005172499796728513 := by
  unfold tailWord_1120950
  simp only [CollatzResearch.WordTrace]
  refine ⟨2555275330562316741472019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27256270192664711909034869 2555275330562316741472019)
  ·
    refine ⟨3832912995843475112208029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2555275330562316741472019 3832912995843475112208029)
    ·
      refine ⟨1437342373441303167078011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3832912995843475112208029 1437342373441303167078011)
      ·
        refine ⟨2156013560161954750617017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1437342373441303167078011 2156013560161954750617017)
        ·
          refine ⟨1617010170121466062962763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2156013560161954750617017 1617010170121466062962763)
          ·
            refine ⟨2425515255182199094444145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1617010170121466062962763 2425515255182199094444145)
            ·
              refine ⟨1819136441386649320833109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2425515255182199094444145 1819136441386649320833109)
              ·
                refine ⟨21318005172499796728513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1819136441386649320833109 21318005172499796728513)
                ·
                  rfl

theorem cell23_1120950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 8].length) (baseStart_1120950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1120950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1120950 prefixEnd_1120950 := by exact prefixLift 1120950
  have htrace : WordTrace (prefixWord ++ tailWord_1120950) baseStart_1120950 baseEnd_1120950 := by
    simpa [prefixWord, tailWord_1120950, baseEnd_1120950] using wordTrace_append hprefix tailTrace_1120950
  have hstable : (prefixWord ++ tailWord_1120950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120950).length < 2 ^ (prefixWord ++ tailWord_1120950).sum := by decide
  have hdescent : baseEnd_1120950 < baseStart_1120950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120953 : List Nat := [1, 2, 1, 4, 1, 1, 1, 4, 3, 3, 2]
def baseStart_1120953 : Nat := 118140960795 + 1120953 * 2 ^ 59
def prefixEnd_1120953 : Nat := 4983230072969 + 3 ^ 40 * 1120953 * 2
def baseEnd_1120953 : Nat := 575587680099457999932337

theorem tailTrace_1120953 : CollatzResearch.WordTrace tailWord_1120953 prefixEnd_1120953 575587680099457999932337 := by
  unfold tailWord_1120953
  simp only [CollatzResearch.WordTrace]
  refine ⟨40884514707986199375911513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27256343138657466250607675 40884514707986199375911513)
  ·
    refine ⟨30663386030989649531933635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40884514707986199375911513 30663386030989649531933635)
    ·
      refine ⟨45995079046484474297900453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30663386030989649531933635 45995079046484474297900453)
      ·
        refine ⟨8624077321215838930856335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45995079046484474297900453 8624077321215838930856335)
        ·
          refine ⟨12936115981823758396284503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8624077321215838930856335 12936115981823758396284503)
          ·
            refine ⟨19404173972735637594426755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12936115981823758396284503 19404173972735637594426755)
            ·
              refine ⟨29106260959103456391640133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19404173972735637594426755 29106260959103456391640133)
              ·
                refine ⟨5457423929831898073432525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29106260959103456391640133 5457423929831898073432525)
                ·
                  refine ⟨2046533973686961777537197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5457423929831898073432525 2046533973686961777537197)
                  ·
                    refine ⟨767450240132610666576449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2046533973686961777537197 767450240132610666576449)
                    ·
                      refine ⟨575587680099457999932337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 767450240132610666576449 575587680099457999932337)
                      ·
                        rfl

theorem cell23_1120953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 3, 3, 2].length) (baseStart_1120953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1120953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1120953 prefixEnd_1120953 := by exact prefixLift 1120953
  have htrace : WordTrace (prefixWord ++ tailWord_1120953) baseStart_1120953 baseEnd_1120953 := by
    simpa [prefixWord, tailWord_1120953, baseEnd_1120953] using wordTrace_append hprefix tailTrace_1120953
  have hstable : (prefixWord ++ tailWord_1120953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120953).length < 2 ^ (prefixWord ++ tailWord_1120953).sum := by decide
  have hdescent : baseEnd_1120953 < baseStart_1120953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120960 : List Nat := [2, 1, 1, 2, 4, 3, 1, 3, 2, 1, 3]
def baseStart_1120960 : Nat := 118140960795 + 1120960 * 2 ^ 59
def prefixEnd_1120960 : Nat := 4983230072969 + 3 ^ 40 * 1120960 * 2
def baseEnd_1120960 : Nat := 575591274464039472544805

theorem tailTrace_1120960 : CollatzResearch.WordTrace tailWord_1120960 prefixEnd_1120960 575591274464039472544805 := by
  unfold tailWord_1120960
  simp only [CollatzResearch.WordTrace]
  refine ⟨20442385009480419785708167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27256513345973893047610889 20442385009480419785708167)
  ·
    refine ⟨30663577514220629678562251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20442385009480419785708167 30663577514220629678562251)
    ·
      refine ⟨45995366271330944517843377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30663577514220629678562251 45995366271330944517843377)
      ·
        refine ⟨34496524703498208388382533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45995366271330944517843377 34496524703498208388382533)
        ·
          refine ⟨6468098381905914072821725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34496524703498208388382533 6468098381905914072821725)
          ·
            refine ⟨2425536893214717777308147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6468098381905914072821725 2425536893214717777308147)
            ·
              refine ⟨3638305339822076665962221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2425536893214717777308147 3638305339822076665962221)
              ·
                refine ⟨1364364502433278749735833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3638305339822076665962221 1364364502433278749735833)
                ·
                  refine ⟨1023273376824959062301875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1364364502433278749735833 1023273376824959062301875)
                  ·
                    refine ⟨1534910065237438593452813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1023273376824959062301875 1534910065237438593452813)
                    ·
                      refine ⟨575591274464039472544805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1534910065237438593452813 575591274464039472544805)
                      ·
                        rfl

theorem cell23_1120960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 3, 2, 1, 3].length) (baseStart_1120960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1120960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1120960 prefixEnd_1120960 := by exact prefixLift 1120960
  have htrace : WordTrace (prefixWord ++ tailWord_1120960) baseStart_1120960 baseEnd_1120960 := by
    simpa [prefixWord, tailWord_1120960, baseEnd_1120960] using wordTrace_append hprefix tailTrace_1120960
  have hstable : (prefixWord ++ tailWord_1120960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120960).length < 2 ^ (prefixWord ++ tailWord_1120960).sum := by decide
  have hdescent : baseEnd_1120960 < baseStart_1120960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120969 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 2, 2, 9]
def baseStart_1120969 : Nat := 118140960795 + 1120969 * 2 ^ 59
def prefixEnd_1120969 : Nat := 4983230072969 + 3 ^ 40 * 1120969 * 2
def baseEnd_1120969 : Nat := 575595895789929937332263

theorem tailTrace_1120969 : CollatzResearch.WordTrace tailWord_1120969 prefixEnd_1120969 575595895789929937332263 := by
  unfold tailWord_1120969
  simp only [CollatzResearch.WordTrace]
  refine ⟨40885098275928234108493961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27256732183952156072329307 40885098275928234108493961)
  ·
    refine ⟨30663823706946175581370471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40885098275928234108493961 30663823706946175581370471)
    ·
      refine ⟨45995735560419263372055707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30663823706946175581370471 45995735560419263372055707)
      ·
        refine ⟨68993603340628895058083561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45995735560419263372055707 68993603340628895058083561)
        ·
          refine ⟨51745202505471671293562671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68993603340628895058083561 51745202505471671293562671)
          ·
            refine ⟨77617803758207506940344007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51745202505471671293562671 77617803758207506940344007)
            ·
              refine ⟨116426705637311260410516011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77617803758207506940344007 116426705637311260410516011)
              ·
                refine ⟨174640058455966890615774017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116426705637311260410516011 174640058455966890615774017)
                ·
                  refine ⟨130980043841975167961830513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 174640058455966890615774017 130980043841975167961830513)
                  ·
                    refine ⟨98235032881481375971372885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 130980043841975167961830513 98235032881481375971372885)
                    ·
                      refine ⟨575595895789929937332263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 98235032881481375971372885 575595895789929937332263)
                      ·
                        rfl

theorem cell23_1120969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 2, 9].length) (baseStart_1120969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1120969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1120969 prefixEnd_1120969 := by exact prefixLift 1120969
  have htrace : WordTrace (prefixWord ++ tailWord_1120969) baseStart_1120969 baseEnd_1120969 := by
    simpa [prefixWord, tailWord_1120969, baseEnd_1120969] using wordTrace_append hprefix tailTrace_1120969
  have hstable : (prefixWord ++ tailWord_1120969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120969).length < 2 ^ (prefixWord ++ tailWord_1120969).sum := by decide
  have hdescent : baseEnd_1120969 < baseStart_1120969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120970 : List Nat := [3, 1, 2, 1, 4, 2, 1, 1, 3, 3, 2]
def baseStart_1120970 : Nat := 118140960795 + 1120970 * 2 ^ 59
def prefixEnd_1120970 : Nat := 4983230072969 + 3 ^ 40 * 1120970 * 2
def baseEnd_1120970 : Nat := 575596409270584433419759

theorem tailTrace_1120970 : CollatzResearch.WordTrace tailWord_1120970 prefixEnd_1120970 575596409270584433419759 := by
  unfold tailWord_1120970
  simp only [CollatzResearch.WordTrace]
  refine ⟨10221283687231152819820091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27256756499283074186186909 10221283687231152819820091)
  ·
    refine ⟨15331925530846729229730137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10221283687231152819820091 15331925530846729229730137)
    ·
      refine ⟨11498944148135046922297603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15331925530846729229730137 11498944148135046922297603)
      ·
        refine ⟨17248416222202570383446405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11498944148135046922297603 17248416222202570383446405)
        ·
          refine ⟨3234078041662981946896201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17248416222202570383446405 3234078041662981946896201)
          ·
            refine ⟨2425558531247236460172151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3234078041662981946896201 2425558531247236460172151)
            ·
              refine ⟨3638337796870854690258227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2425558531247236460172151 3638337796870854690258227)
              ·
                refine ⟨5457506695306282035387341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3638337796870854690258227 5457506695306282035387341)
                ·
                  refine ⟨2046565010739855763270253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5457506695306282035387341 2046565010739855763270253)
                  ·
                    refine ⟨767461879027445911226345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2046565010739855763270253 767461879027445911226345)
                    ·
                      refine ⟨575596409270584433419759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 767461879027445911226345 575596409270584433419759)
                      ·
                        rfl

theorem cell23_1120970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 3, 3, 2].length) (baseStart_1120970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1120970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1120970 prefixEnd_1120970 := by exact prefixLift 1120970
  have htrace : WordTrace (prefixWord ++ tailWord_1120970) baseStart_1120970 baseEnd_1120970 := by
    simpa [prefixWord, tailWord_1120970, baseEnd_1120970] using wordTrace_append hprefix tailTrace_1120970
  have hstable : (prefixWord ++ tailWord_1120970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120970).length < 2 ^ (prefixWord ++ tailWord_1120970).sum := by decide
  have hdescent : baseEnd_1120970 < baseStart_1120970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120979 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 10]
def baseStart_1120979 : Nat := 118140960795 + 1120979 * 2 ^ 59
def prefixEnd_1120979 : Nat := 4983230072969 + 3 ^ 40 * 1120979 * 2
def baseEnd_1120979 : Nat := 575601030596474898207217

theorem tailTrace_1120979 : CollatzResearch.WordTrace tailWord_1120979 prefixEnd_1120979 575601030596474898207217 := by
  unfold tailWord_1120979
  simp only [CollatzResearch.WordTrace]
  refine ⟨40885463005892005816357991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27256975337261337210905327 40885463005892005816357991)
  ·
    refine ⟨61328194508838008724536987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40885463005892005816357991 61328194508838008724536987)
    ·
      refine ⟨91992291763257013086805481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61328194508838008724536987 91992291763257013086805481)
      ·
        refine ⟨68994218822442759815104111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91992291763257013086805481 68994218822442759815104111)
        ·
          refine ⟨103491328233664139722656167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68994218822442759815104111 103491328233664139722656167)
          ·
            refine ⟨155236992350496209583984251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103491328233664139722656167 155236992350496209583984251)
            ·
              refine ⟨232855488525744314375976377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155236992350496209583984251 232855488525744314375976377)
              ·
                refine ⟨174641616394308235781982283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 232855488525744314375976377 174641616394308235781982283)
                ·
                  refine ⟨261962424591462353672973425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 174641616394308235781982283 261962424591462353672973425)
                  ·
                    refine ⟨196471818443596765254730069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 261962424591462353672973425 196471818443596765254730069)
                    ·
                      refine ⟨575601030596474898207217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 196471818443596765254730069 575601030596474898207217)
                      ·
                        rfl

theorem cell23_1120979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 10].length) (baseStart_1120979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1120979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1120979 prefixEnd_1120979 := by exact prefixLift 1120979
  have htrace : WordTrace (prefixWord ++ tailWord_1120979) baseStart_1120979 baseEnd_1120979 := by
    simpa [prefixWord, tailWord_1120979, baseEnd_1120979] using wordTrace_append hprefix tailTrace_1120979
  have hstable : (prefixWord ++ tailWord_1120979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120979).length < 2 ^ (prefixWord ++ tailWord_1120979).sum := by decide
  have hdescent : baseEnd_1120979 < baseStart_1120979 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120983 : List Nat := [1, 1, 3, 2, 1, 4, 1, 1, 3, 4, 2]
def baseStart_1120983 : Nat := 118140960795 + 1120983 * 2 ^ 59
def prefixEnd_1120983 : Nat := 4983230072969 + 3 ^ 40 * 1120983 * 2
def baseEnd_1120983 : Nat := 575603084519092882557199

theorem tailTrace_1120983 : CollatzResearch.WordTrace tailWord_1120983 prefixEnd_1120983 575603084519092882557199 := by
  unfold tailWord_1120983
  simp only [CollatzResearch.WordTrace]
  refine ⟨40885608897877514499503603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27257072598585009666335735 40885608897877514499503603)
  ·
    refine ⟨61328413346816271749255405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40885608897877514499503603 61328413346816271749255405)
    ·
      refine ⟨22998155005056101905970777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61328413346816271749255405 22998155005056101905970777)
      ·
        refine ⟨17248616253792076429478083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22998155005056101905970777 17248616253792076429478083)
        ·
          refine ⟨25872924380688114644217125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17248616253792076429478083 25872924380688114644217125)
          ·
            refine ⟨4851173321379021495790711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25872924380688114644217125 4851173321379021495790711)
            ·
              refine ⟨7276759982068532243686067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4851173321379021495790711 7276759982068532243686067)
              ·
                refine ⟨10915139973102798365529101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7276759982068532243686067 10915139973102798365529101)
                ·
                  refine ⟨4093177489913549387073413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10915139973102798365529101 4093177489913549387073413)
                  ·
                    refine ⟨767470779358790510076265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4093177489913549387073413 767470779358790510076265)
                    ·
                      refine ⟨575603084519092882557199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 767470779358790510076265 575603084519092882557199)
                      ·
                        rfl

theorem cell23_1120983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 3, 4, 2].length) (baseStart_1120983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1120983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1120983 prefixEnd_1120983 := by exact prefixLift 1120983
  have htrace : WordTrace (prefixWord ++ tailWord_1120983) baseStart_1120983 baseEnd_1120983 := by
    simpa [prefixWord, tailWord_1120983, baseEnd_1120983] using wordTrace_append hprefix tailTrace_1120983
  have hstable : (prefixWord ++ tailWord_1120983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120983).length < 2 ^ (prefixWord ++ tailWord_1120983).sum := by decide
  have hdescent : baseEnd_1120983 < baseStart_1120983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120986 : List Nat := [3, 1, 1, 2, 2, 2, 1, 3, 2, 1, 5]
def baseStart_1120986 : Nat := 118140960795 + 1120986 * 2 ^ 59
def prefixEnd_1120986 : Nat := 4983230072969 + 3 ^ 40 * 1120986 * 2
def baseEnd_1120986 : Nat := 575604624961056370819685

theorem tailTrace_1120986 : CollatzResearch.WordTrace tailWord_1120986 prefixEnd_1120986 575604624961056370819685 := by
  unfold tailWord_1120986
  simp only [CollatzResearch.WordTrace]
  refine ⟨10221429579216661502965703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27257145544577764007908541 10221429579216661502965703)
  ·
    refine ⟨15332144368824992254448555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10221429579216661502965703 15332144368824992254448555)
    ·
      refine ⟨22998216553237488381672833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15332144368824992254448555 22998216553237488381672833)
      ·
        refine ⟨17248662414928116286254625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22998216553237488381672833 17248662414928116286254625)
        ·
          refine ⟨12936496811196087214690969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17248662414928116286254625 12936496811196087214690969)
          ·
            refine ⟨9702372608397065411018227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12936496811196087214690969 9702372608397065411018227)
            ·
              refine ⟨14553558912595598116527341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9702372608397065411018227 14553558912595598116527341)
              ·
                refine ⟨5457584592223349293697753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14553558912595598116527341 5457584592223349293697753)
                ·
                  refine ⟨4093188444167511970273315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5457584592223349293697753 4093188444167511970273315)
                  ·
                    refine ⟨6139782666251267955409973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4093188444167511970273315 6139782666251267955409973)
                    ·
                      refine ⟨575604624961056370819685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6139782666251267955409973 575604624961056370819685)
                      ·
                        rfl

theorem cell23_1120986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 2, 1, 5].length) (baseStart_1120986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1120986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1120986 prefixEnd_1120986 := by exact prefixLift 1120986
  have htrace : WordTrace (prefixWord ++ tailWord_1120986) baseStart_1120986 baseEnd_1120986 := by
    simpa [prefixWord, tailWord_1120986, baseEnd_1120986] using wordTrace_append hprefix tailTrace_1120986
  have hstable : (prefixWord ++ tailWord_1120986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120986).length < 2 ^ (prefixWord ++ tailWord_1120986).sum := by decide
  have hdescent : baseEnd_1120986 < baseStart_1120986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121096 : List Nat := [2, 1, 3, 1, 1, 3, 1, 1, 10]
def baseStart_1121096 : Nat := 118140960795 + 1121096 * 2 ^ 59
def prefixEnd_1121096 : Nat := 4983230072969 + 3 ^ 40 * 1121096 * 2
def baseEnd_1121096 : Nat := 63962345314783437827131

theorem tailTrace_1121096 : CollatzResearch.WordTrace tailWord_1121096 prefixEnd_1121096 63962345314783437827131 := by
  unfold tailWord_1121096
  simp only [CollatzResearch.WordTrace]
  refine ⟨20444865173234067399183571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27259820230978756532244761 20444865173234067399183571)
  ·
    refine ⟨30667297759851101098775357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20444865173234067399183571 30667297759851101098775357)
    ·
      refine ⟨11500236659944162912040759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30667297759851101098775357 11500236659944162912040759)
      ·
        refine ⟨17250354989916244368061139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11500236659944162912040759 17250354989916244368061139)
        ·
          refine ⟨25875532484874366552091709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17250354989916244368061139 25875532484874366552091709)
          ·
            refine ⟨9703324681827887457034391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25875532484874366552091709 9703324681827887457034391)
            ·
              refine ⟨14554987022741831185551587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9703324681827887457034391 14554987022741831185551587)
              ·
                refine ⟨21832480534112746778327381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14554987022741831185551587 21832480534112746778327381)
                ·
                  refine ⟨63962345314783437827131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 21832480534112746778327381 63962345314783437827131)
                  ·
                    rfl

theorem cell23_1121096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 10].length) (baseStart_1121096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1121096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1121096 prefixEnd_1121096 := by exact prefixLift 1121096
  have htrace : WordTrace (prefixWord ++ tailWord_1121096) baseStart_1121096 baseEnd_1121096 := by
    simpa [prefixWord, tailWord_1121096, baseEnd_1121096] using wordTrace_append hprefix tailTrace_1121096
  have hstable : (prefixWord ++ tailWord_1121096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121096).length < 2 ^ (prefixWord ++ tailWord_1121096).sum := by decide
  have hdescent : baseEnd_1121096 < baseStart_1121096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121201 : List Nat := [1, 2, 2, 4, 4, 1, 1, 1, 2, 3, 2]
def baseStart_1121201 : Nat := 118140960795 + 1121201 * 2 ^ 59
def prefixEnd_1121201 : Nat := 4983230072969 + 3 ^ 40 * 1121201 * 2
def baseEnd_1121201 : Nat := 575715023301773029631197

theorem tailTrace_1121201 : CollatzResearch.WordTrace tailWord_1121201 prefixEnd_1121201 575715023301773029631197 := by
  unfold tailWord_1121201
  simp only [CollatzResearch.WordTrace]
  refine ⟨40893560011087737730939457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27262373340725158487292971 40893560011087737730939457)
  ·
    refine ⟨30670170008315803298204593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40893560011087737730939457 30670170008315803298204593)
    ·
      refine ⟨23002627506236852473653445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30670170008315803298204593 23002627506236852473653445)
      ·
        refine ⟨4312992657419409838810021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23002627506236852473653445 4312992657419409838810021)
        ·
          refine ⟨808686123266139344776879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4312992657419409838810021 808686123266139344776879)
          ·
            refine ⟨1213029184899209017165319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 808686123266139344776879 1213029184899209017165319)
            ·
              refine ⟨1819543777348813525747979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1213029184899209017165319 1819543777348813525747979)
              ·
                refine ⟨2729315666023220288621969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1819543777348813525747979 2729315666023220288621969)
                ·
                  refine ⟨2046986749517415216466477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2729315666023220288621969 2046986749517415216466477)
                  ·
                    refine ⟨767620031069030706174929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2046986749517415216466477 767620031069030706174929)
                    ·
                      refine ⟨575715023301773029631197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 767620031069030706174929 575715023301773029631197)
                      ·
                        rfl

theorem cell23_1121201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 1, 2, 3, 2].length) (baseStart_1121201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1121201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1121201 prefixEnd_1121201 := by exact prefixLift 1121201
  have htrace : WordTrace (prefixWord ++ tailWord_1121201) baseStart_1121201 baseEnd_1121201 := by
    simpa [prefixWord, tailWord_1121201, baseEnd_1121201] using wordTrace_append hprefix tailTrace_1121201
  have hstable : (prefixWord ++ tailWord_1121201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121201).length < 2 ^ (prefixWord ++ tailWord_1121201).sum := by decide
  have hdescent : baseEnd_1121201 < baseStart_1121201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121224 : List Nat := [2, 1, 3, 1, 5, 2, 1, 2, 2, 4]
def baseStart_1121224 : Nat := 118140960795 + 1121224 * 2 ^ 59
def prefixEnd_1121224 : Nat := 4983230072969 + 3 ^ 40 * 1121224 * 2
def baseEnd_1121224 : Nat := 191908944452275479881197

theorem tailTrace_1121224 : CollatzResearch.WordTrace tailWord_1121224 prefixEnd_1121224 191908944452275479881197 := by
  unfold tailWord_1121224
  simp only [CollatzResearch.WordTrace]
  refine ⟨20447199445002206329513363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27262932593336275106017817 20447199445002206329513363)
  ·
    refine ⟨30670799167503309494270045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20447199445002206329513363 30670799167503309494270045)
    ·
      refine ⟨11501549687813741060351267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30670799167503309494270045 11501549687813741060351267)
      ·
        refine ⟨17252324531720611590526901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11501549687813741060351267 17252324531720611590526901)
        ·
          refine ⟨1617405424848807336611897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17252324531720611590526901 1617405424848807336611897)
          ·
            refine ⟨1213054068636605502458923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1617405424848807336611897 1213054068636605502458923)
            ·
              refine ⟨1819581102954908253688385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1213054068636605502458923 1819581102954908253688385)
              ·
                refine ⟨1364685827216181190266289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1819581102954908253688385 1364685827216181190266289)
                ·
                  refine ⟨1023514370412135892699717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1364685827216181190266289 1023514370412135892699717)
                  ·
                    refine ⟨191908944452275479881197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1023514370412135892699717 191908944452275479881197)
                    ·
                      rfl

theorem cell23_1121224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 2, 2, 4].length) (baseStart_1121224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1121224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1121224 prefixEnd_1121224 := by exact prefixLift 1121224
  have htrace : WordTrace (prefixWord ++ tailWord_1121224) baseStart_1121224 baseEnd_1121224 := by
    simpa [prefixWord, tailWord_1121224, baseEnd_1121224] using wordTrace_append hprefix tailTrace_1121224
  have hstable : (prefixWord ++ tailWord_1121224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121224).length < 2 ^ (prefixWord ++ tailWord_1121224).sum := by decide
  have hdescent : baseEnd_1121224 < baseStart_1121224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121268 : List Nat := [2, 6, 2, 1, 1, 1, 2, 1, 1, 1, 5]
def baseStart_1121268 : Nat := 118140960795 + 1121268 * 2 ^ 59
def prefixEnd_1121268 : Nat := 4983230072969 + 3 ^ 40 * 1121268 * 2
def baseEnd_1121268 : Nat := 575749426505624267493389

theorem tailTrace_1121268 : CollatzResearch.WordTrace tailWord_1121268 prefixEnd_1121268 575749426505624267493389 := by
  unfold tailWord_1121268
  simp only [CollatzResearch.WordTrace]
  refine ⟨20448001850922504086814229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27264002467896672115752305 20448001850922504086814229)
  ·
    refine ⟨958500086761992379069417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 20448001850922504086814229 958500086761992379069417)
    ·
      refine ⟨718875065071494284302063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 958500086761992379069417 718875065071494284302063)
      ·
        refine ⟨1078312597607241426453095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 718875065071494284302063 1078312597607241426453095)
        ·
          refine ⟨1617468896410862139679643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1078312597607241426453095 1617468896410862139679643)
          ·
            refine ⟨2426203344616293209519465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1617468896410862139679643 2426203344616293209519465)
            ·
              refine ⟨1819652508462219907139599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2426203344616293209519465 1819652508462219907139599)
              ·
                refine ⟨2729478762693329860709399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1819652508462219907139599 2729478762693329860709399)
                ·
                  refine ⟨4094218144039994791064099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2729478762693329860709399 4094218144039994791064099)
                  ·
                    refine ⟨6141327216059992186596149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4094218144039994791064099 6141327216059992186596149)
                    ·
                      refine ⟨575749426505624267493389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6141327216059992186596149 575749426505624267493389)
                      ·
                        rfl

theorem cell23_1121268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_1121268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1121268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1121268 prefixEnd_1121268 := by exact prefixLift 1121268
  have htrace : WordTrace (prefixWord ++ tailWord_1121268) baseStart_1121268 baseEnd_1121268 := by
    simpa [prefixWord, tailWord_1121268, baseEnd_1121268] using wordTrace_append hprefix tailTrace_1121268
  have hstable : (prefixWord ++ tailWord_1121268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121268).length < 2 ^ (prefixWord ++ tailWord_1121268).sum := by decide
  have hdescent : baseEnd_1121268 < baseStart_1121268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121282 : List Nat := [3, 4, 1, 3, 1, 1, 3, 2, 1, 2, 2]
def baseStart_1121282 : Nat := 118140960795 + 1121282 * 2 ^ 59
def prefixEnd_1121282 : Nat := 4983230072969 + 3 ^ 40 * 1121282 * 2
def baseEnd_1121282 : Nat := 575756615234787212718325

theorem tailTrace_1121282 : CollatzResearch.WordTrace tailWord_1121282 prefixEnd_1121282 575756615234787212718325 := by
  unfold tailWord_1121282
  simp only [CollatzResearch.WordTrace]
  refine ⟨10224128580948572141159525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27264342882529525709758733 10224128580948572141159525)
  ·
    refine ⟨1917024108927857276467411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10224128580948572141159525 1917024108927857276467411)
    ·
      refine ⟨2875536163391785914701117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1917024108927857276467411 2875536163391785914701117)
      ·
        refine ⟨1078326061271919718012919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2875536163391785914701117 1078326061271919718012919)
        ·
          refine ⟨1617489091907879577019379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1078326061271919718012919 1617489091907879577019379)
          ·
            refine ⟨2426233637861819365529069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1617489091907879577019379 2426233637861819365529069)
            ·
              refine ⟨909837614198182262073401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2426233637861819365529069 909837614198182262073401)
              ·
                refine ⟨682378210648636696555051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 909837614198182262073401 682378210648636696555051)
                ·
                  refine ⟨1023567315972955044832577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 682378210648636696555051 1023567315972955044832577)
                  ·
                    refine ⟨767675486979716283624433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1023567315972955044832577 767675486979716283624433)
                    ·
                      refine ⟨575756615234787212718325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 767675486979716283624433 575756615234787212718325)
                      ·
                        rfl

theorem cell23_1121282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_1121282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1121282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1121282 prefixEnd_1121282 := by exact prefixLift 1121282
  have htrace : WordTrace (prefixWord ++ tailWord_1121282) baseStart_1121282 baseEnd_1121282 := by
    simpa [prefixWord, tailWord_1121282, baseEnd_1121282] using wordTrace_append hprefix tailTrace_1121282
  have hstable : (prefixWord ++ tailWord_1121282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121282).length < 2 ^ (prefixWord ++ tailWord_1121282).sum := by decide
  have hdescent : baseEnd_1121282 < baseStart_1121282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121308 : List Nat := [2, 2, 3, 1, 5, 1, 1, 2, 1, 3, 2]
def baseStart_1121308 : Nat := 118140960795 + 1121308 * 2 ^ 59
def prefixEnd_1121308 : Nat := 4983230072969 + 3 ^ 40 * 1121308 * 2
def baseEnd_1121308 : Nat := 575769965731804110993205

theorem tailTrace_1121308 : CollatzResearch.WordTrace tailWord_1121308 prefixEnd_1121308 575769965731804110993205 := by
  unfold tailWord_1121308
  simp only [CollatzResearch.WordTrace]
  refine ⟨20448731310850047502542289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27264975081133396670056385 20448731310850047502542289)
  ·
    refine ⟨15336548483137535626906717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20448731310850047502542289 15336548483137535626906717)
    ·
      refine ⟨5751205681176575860090019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15336548483137535626906717 5751205681176575860090019)
      ·
        refine ⟨8626808521764863790135029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5751205681176575860090019 8626808521764863790135029)
        ·
          refine ⟨808763298915455980325159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8626808521764863790135029 808763298915455980325159)
          ·
            refine ⟨1213144948373183970487739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 808763298915455980325159 1213144948373183970487739)
            ·
              refine ⟨1819717422559775955731609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1213144948373183970487739 1819717422559775955731609)
              ·
                refine ⟨1364788066919831966798707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1819717422559775955731609 1364788066919831966798707)
                ·
                  refine ⟨2047182100379747950198061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1364788066919831966798707 2047182100379747950198061)
                  ·
                    refine ⟨767693287642405481324273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2047182100379747950198061 767693287642405481324273)
                    ·
                      refine ⟨575769965731804110993205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 767693287642405481324273 575769965731804110993205)
                      ·
                        rfl

theorem cell23_1121308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 2, 1, 3, 2].length) (baseStart_1121308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1121308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1121308 prefixEnd_1121308 := by exact prefixLift 1121308
  have htrace : WordTrace (prefixWord ++ tailWord_1121308) baseStart_1121308 baseEnd_1121308 := by
    simpa [prefixWord, tailWord_1121308, baseEnd_1121308] using wordTrace_append hprefix tailTrace_1121308
  have hstable : (prefixWord ++ tailWord_1121308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121308).length < 2 ^ (prefixWord ++ tailWord_1121308).sum := by decide
  have hdescent : baseEnd_1121308 < baseStart_1121308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121360 : List Nat := [2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 4]
def baseStart_1121360 : Nat := 118140960795 + 1121360 * 2 ^ 59
def prefixEnd_1121360 : Nat := 4983230072969 + 3 ^ 40 * 1121360 * 2
def baseEnd_1121360 : Nat := 575796666725837907542965

theorem tailTrace_1121360 : CollatzResearch.WordTrace tailWord_1121360 prefixEnd_1121360 575796666725837907542965 := by
  unfold tailWord_1121360
  simp only [CollatzResearch.WordTrace]
  refine ⟨20449679608755853942988767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27266239478341138590651689 20449679608755853942988767)
  ·
    refine ⟨30674519413133780914483151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20449679608755853942988767 30674519413133780914483151)
    ·
      refine ⟨46011779119700671371724727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30674519413133780914483151 46011779119700671371724727)
      ·
        refine ⟨69017668679551007057587091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46011779119700671371724727 69017668679551007057587091)
        ·
          refine ⟨103526503019326510586380637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69017668679551007057587091 103526503019326510586380637)
          ·
            refine ⟨38822438632247441469892739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103526503019326510586380637 38822438632247441469892739)
            ·
              refine ⟨58233657948371162204839109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38822438632247441469892739 58233657948371162204839109)
              ·
                refine ⟨10918810865319592913407333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58233657948371162204839109 10918810865319592913407333)
                ·
                  refine ⟨2047277037247423671263875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10918810865319592913407333 2047277037247423671263875)
                  ·
                    refine ⟨3070915555871135506895813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2047277037247423671263875 3070915555871135506895813)
                    ·
                      refine ⟨575796666725837907542965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3070915555871135506895813 575796666725837907542965)
                      ·
                        rfl

theorem cell23_1121360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 4].length) (baseStart_1121360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1121360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1121360 prefixEnd_1121360 := by exact prefixLift 1121360
  have htrace : WordTrace (prefixWord ++ tailWord_1121360) baseStart_1121360 baseEnd_1121360 := by
    simpa [prefixWord, tailWord_1121360, baseEnd_1121360] using wordTrace_append hprefix tailTrace_1121360
  have hstable : (prefixWord ++ tailWord_1121360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121360).length < 2 ^ (prefixWord ++ tailWord_1121360).sum := by decide
  have hdescent : baseEnd_1121360 < baseStart_1121360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121377 : List Nat := [1, 2, 3, 1, 1, 2, 5, 1, 2, 1, 4]
def baseStart_1121377 : Nat := 118140960795 + 1121377 * 2 ^ 59
def prefixEnd_1121377 : Nat := 4983230072969 + 3 ^ 40 * 1121377 * 2
def baseEnd_1121377 : Nat := 575805395896964341030387

theorem tailTrace_1121377 : CollatzResearch.WordTrace tailWord_1121377 prefixEnd_1121377 575805395896964341030387 := by
  unfold tailWord_1121377
  simp only [CollatzResearch.WordTrace]
  refine ⟨40899979258450119789346385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27266652838966746526230923 40899979258450119789346385)
  ·
    refine ⟨30674984443837589842009789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40899979258450119789346385 30674984443837589842009789)
    ·
      refine ⟨11503119166439096190753671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30674984443837589842009789 11503119166439096190753671)
      ·
        refine ⟨17254678749658644286130507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11503119166439096190753671 17254678749658644286130507)
        ·
          refine ⟨25882018124487966429195761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17254678749658644286130507 25882018124487966429195761)
          ·
            refine ⟨19411513593365974821896821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25882018124487966429195761 19411513593365974821896821)
            ·
              refine ⟨1819829399378060139552827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19411513593365974821896821 1819829399378060139552827)
              ·
                refine ⟨2729744099067090209329241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1819829399378060139552827 2729744099067090209329241)
                ·
                  refine ⟨2047308074300317656996931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2729744099067090209329241 2047308074300317656996931)
                  ·
                    refine ⟨3070962111450476485495397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2047308074300317656996931 3070962111450476485495397)
                    ·
                      refine ⟨575805395896964341030387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3070962111450476485495397 575805395896964341030387)
                      ·
                        rfl

theorem cell23_1121377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 1, 2, 1, 4].length) (baseStart_1121377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1121377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1121377 prefixEnd_1121377 := by exact prefixLift 1121377
  have htrace : WordTrace (prefixWord ++ tailWord_1121377) baseStart_1121377 baseEnd_1121377 := by
    simpa [prefixWord, tailWord_1121377, baseEnd_1121377] using wordTrace_append hprefix tailTrace_1121377
  have hstable : (prefixWord ++ tailWord_1121377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121377).length < 2 ^ (prefixWord ++ tailWord_1121377).sum := by decide
  have hdescent : baseEnd_1121377 < baseStart_1121377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121404 : List Nat := [2, 2, 2, 1, 1, 3, 1, 6, 1, 4]
def baseStart_1121404 : Nat := 118140960795 + 1121404 * 2 ^ 59
def prefixEnd_1121404 : Nat := 4983230072969 + 3 ^ 40 * 1121404 * 2
def baseEnd_1121404 : Nat := 191939753291545245130921

theorem tailTrace_1121404 : CollatzResearch.WordTrace tailWord_1121404 prefixEnd_1121404 191939753291545245130921 := by
  unfold tailWord_1121404
  simp only [CollatzResearch.WordTrace]
  refine ⟨20450482014676151700289633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27267309352901535600386177 20450482014676151700289633)
  ·
    refine ⟨15337861511007113775217225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20450482014676151700289633 15337861511007113775217225)
    ·
      refine ⟨11503396133255335331412919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15337861511007113775217225 11503396133255335331412919)
      ·
        refine ⟨17255094199883002997119379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11503396133255335331412919 17255094199883002997119379)
        ·
          refine ⟨25882641299824504495679069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17255094199883002997119379 25882641299824504495679069)
          ·
            refine ⟨9705990487434189185879651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25882641299824504495679069 9705990487434189185879651)
            ·
              refine ⟨14558985731151283778819477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9705990487434189185879651 14558985731151283778819477)
              ·
                refine ⟨682452456147716427132163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14558985731151283778819477 682452456147716427132163)
                ·
                  refine ⟨1023678684221574640698245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 682452456147716427132163 1023678684221574640698245)
                  ·
                    refine ⟨191939753291545245130921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1023678684221574640698245 191939753291545245130921)
                    ·
                      rfl

theorem cell23_1121404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 6, 1, 4].length) (baseStart_1121404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1121404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1121404 prefixEnd_1121404 := by exact prefixLift 1121404
  have htrace : WordTrace (prefixWord ++ tailWord_1121404) baseStart_1121404 baseEnd_1121404 := by
    simpa [prefixWord, tailWord_1121404, baseEnd_1121404] using wordTrace_append hprefix tailTrace_1121404
  have hstable : (prefixWord ++ tailWord_1121404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121404).length < 2 ^ (prefixWord ++ tailWord_1121404).sum := by decide
  have hdescent : baseEnd_1121404 < baseStart_1121404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121438 : List Nat := [4, 3, 1, 1, 2, 1, 3, 3, 1, 4]
def baseStart_1121438 : Nat := 118140960795 + 1121438 * 2 ^ 59
def prefixEnd_1121438 : Nat := 4983230072969 + 3 ^ 40 * 1121438 * 2
def baseEnd_1121438 : Nat := 191945572738962867455869

theorem tailTrace_1121438 : CollatzResearch.WordTrace tailWord_1121438 prefixEnd_1121438 191945572738962867455869 := by
  unfold tailWord_1121438
  simp only [CollatzResearch.WordTrace]
  refine ⟨5112775513903640900914621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27268136074152751471544645 5112775513903640900914621)
  ·
    refine ⟨1917290817713865337842983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5112775513903640900914621 1917290817713865337842983)
    ·
      refine ⟨2875936226570798006764475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1917290817713865337842983 2875936226570798006764475)
      ·
        refine ⟨4313904339856197010146713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2875936226570798006764475 4313904339856197010146713)
        ·
          refine ⟨3235428254892147757610035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4313904339856197010146713 3235428254892147757610035)
          ·
            refine ⟨4853142382338221636415053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3235428254892147757610035 4853142382338221636415053)
            ·
              refine ⟨1819928393376833113655645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4853142382338221636415053 1819928393376833113655645)
              ·
                refine ⟨682473147516312417620867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1819928393376833113655645 682473147516312417620867)
                ·
                  refine ⟨1023709721274468626431301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 682473147516312417620867 1023709721274468626431301)
                  ·
                    refine ⟨191945572738962867455869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1023709721274468626431301 191945572738962867455869)
                    ·
                      rfl

theorem cell23_1121438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_1121438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1121438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1121438 prefixEnd_1121438 := by exact prefixLift 1121438
  have htrace : WordTrace (prefixWord ++ tailWord_1121438) baseStart_1121438 baseEnd_1121438 := by
    simpa [prefixWord, tailWord_1121438, baseEnd_1121438] using wordTrace_append hprefix tailTrace_1121438
  have hstable : (prefixWord ++ tailWord_1121438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121438).length < 2 ^ (prefixWord ++ tailWord_1121438).sum := by decide
  have hdescent : baseEnd_1121438 < baseStart_1121438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121467 : List Nat := [1, 1, 1, 1, 1, 2, 4, 2, 2, 6, 2]
def baseStart_1121467 : Nat := 118140960795 + 1121467 * 2 ^ 59
def prefixEnd_1121467 : Nat := 4983230072969 + 3 ^ 40 * 1121467 * 2
def baseEnd_1121467 : Nat := 575851609155868988904973

theorem tailTrace_1121467 : CollatzResearch.WordTrace tailWord_1121467 prefixEnd_1121467 575851609155868988904973 := by
  unfold tailWord_1121467
  simp only [CollatzResearch.WordTrace]
  refine ⟨40903261828124065160122655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27268841218749376773415103 40903261828124065160122655)
  ·
    refine ⟨61354892742186097740183983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40903261828124065160122655 61354892742186097740183983)
    ·
      refine ⟨92032339113279146610275975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61354892742186097740183983 92032339113279146610275975)
      ·
        refine ⟨138048508669918719915413963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92032339113279146610275975 138048508669918719915413963)
        ·
          refine ⟨207072763004878079873120945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138048508669918719915413963 207072763004878079873120945)
          ·
            refine ⟨155304572253658559904840709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 207072763004878079873120945 155304572253658559904840709)
            ·
              refine ⟨29119607297560979982157633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 155304572253658559904840709 29119607297560979982157633)
              ·
                refine ⟨21839705473170734986618225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29119607297560979982157633 21839705473170734986618225)
                ·
                  refine ⟨16379779104878051239963669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21839705473170734986618225 16379779104878051239963669)
                  ·
                    refine ⟨767802145541158651873297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16379779104878051239963669 767802145541158651873297)
                    ·
                      refine ⟨575851609155868988904973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 767802145541158651873297 575851609155868988904973)
                      ·
                        rfl

theorem cell23_1121467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 6, 2].length) (baseStart_1121467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1121467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1121467 prefixEnd_1121467 := by exact prefixLift 1121467
  have htrace : WordTrace (prefixWord ++ tailWord_1121467) baseStart_1121467 baseEnd_1121467 := by
    simpa [prefixWord, tailWord_1121467, baseEnd_1121467] using wordTrace_append hprefix tailTrace_1121467
  have hstable : (prefixWord ++ tailWord_1121467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121467).length < 2 ^ (prefixWord ++ tailWord_1121467).sum := by decide
  have hdescent : baseEnd_1121467 < baseStart_1121467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121504 : List Nat := [2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 5]
def baseStart_1121504 : Nat := 118140960795 + 1121504 * 2 ^ 59
def prefixEnd_1121504 : Nat := 4983230072969 + 3 ^ 40 * 1121504 * 2
def baseEnd_1121504 : Nat := 575870607940085344142303

theorem tailTrace_1121504 : CollatzResearch.WordTrace tailWord_1121504 prefixEnd_1121504 575870607940085344142303 := by
  unfold tailWord_1121504
  simp only [CollatzResearch.WordTrace]
  refine ⟨20452305664495010239609783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27269740885993346986146377 20452305664495010239609783)
  ·
    refine ⟨30678458496742515359414675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20452305664495010239609783 30678458496742515359414675)
    ·
      refine ⟨46017687745113773039122013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30678458496742515359414675 46017687745113773039122013)
      ·
        refine ⟨17256632904417664889670755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46017687745113773039122013 17256632904417664889670755)
        ·
          refine ⟨25884949356626497334506133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17256632904417664889670755 25884949356626497334506133)
          ·
            refine ⟨1213357001091867062554975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 25884949356626497334506133 1213357001091867062554975)
            ·
              refine ⟨1820035501637800593832463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1213357001091867062554975 1820035501637800593832463)
              ·
                refine ⟨2730053252456700890748695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1820035501637800593832463 2730053252456700890748695)
                ·
                  refine ⟨4095079878685051336123043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2730053252456700890748695 4095079878685051336123043)
                  ·
                    refine ⟨6142619818027577004184565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4095079878685051336123043 6142619818027577004184565)
                    ·
                      refine ⟨575870607940085344142303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6142619818027577004184565 575870607940085344142303)
                      ·
                        rfl

theorem cell23_1121504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 5].length) (baseStart_1121504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1121504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1121504 prefixEnd_1121504 := by exact prefixLift 1121504
  have htrace : WordTrace (prefixWord ++ tailWord_1121504) baseStart_1121504 baseEnd_1121504 := by
    simpa [prefixWord, tailWord_1121504, baseEnd_1121504] using wordTrace_append hprefix tailTrace_1121504
  have hstable : (prefixWord ++ tailWord_1121504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121504).length < 2 ^ (prefixWord ++ tailWord_1121504).sum := by decide
  have hdescent : baseEnd_1121504 < baseStart_1121504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121577 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 6, 4, 3]
def baseStart_1121577 : Nat := 118140960795 + 1121577 * 2 ^ 59
def prefixEnd_1121577 : Nat := 4983230072969 + 3 ^ 40 * 1121577 * 2
def baseEnd_1121577 : Nat := 575908092027863558529467

theorem tailTrace_1121577 : CollatzResearch.WordTrace tailWord_1121577 prefixEnd_1121577 575908092027863558529467 := by
  unfold tailWord_1121577
  simp only [CollatzResearch.WordTrace]
  refine ⟨40907273857725553946626985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27271515905150369297751323 40907273857725553946626985)
  ·
    refine ⟨30680455393294165459970239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40907273857725553946626985 30680455393294165459970239)
    ·
      refine ⟨46020683089941248189955359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30680455393294165459970239 46020683089941248189955359)
      ·
        refine ⟨69031024634911872284933039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46020683089941248189955359 69031024634911872284933039)
        ·
          refine ⟨103546536952367808427399559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69031024634911872284933039 103546536952367808427399559)
          ·
            refine ⟨155319805428551712641099339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103546536952367808427399559 155319805428551712641099339)
            ·
              refine ⟨232979708142827568961649009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155319805428551712641099339 232979708142827568961649009)
              ·
                refine ⟨174734781107120676721236757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 232979708142827568961649009 174734781107120676721236757)
                ·
                  refine ⟨8190692864396281721307973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 174734781107120676721236757 8190692864396281721307973)
                  ·
                    refine ⟨1535754912074302822745245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8190692864396281721307973 1535754912074302822745245)
                    ·
                      refine ⟨575908092027863558529467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1535754912074302822745245 575908092027863558529467)
                      ·
                        rfl

theorem cell23_1121577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 4, 3].length) (baseStart_1121577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1121577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1121577 prefixEnd_1121577 := by exact prefixLift 1121577
  have htrace : WordTrace (prefixWord ++ tailWord_1121577) baseStart_1121577 baseEnd_1121577 := by
    simpa [prefixWord, tailWord_1121577, baseEnd_1121577] using wordTrace_append hprefix tailTrace_1121577
  have hstable : (prefixWord ++ tailWord_1121577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121577).length < 2 ^ (prefixWord ++ tailWord_1121577).sum := by decide
  have hdescent : baseEnd_1121577 < baseStart_1121577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121657 : List Nat := [1, 2, 1, 3, 2, 1, 2, 1, 2, 8]
def baseStart_1121657 : Nat := 118140960795 + 1121657 * 2 ^ 59
def prefixEnd_1121657 : Nat := 4983230072969 + 3 ^ 40 * 1121657 * 2
def baseEnd_1121657 : Nat := 191983056826741081843033

theorem tailTrace_1121657 : CollatzResearch.WordTrace tailWord_1121657 prefixEnd_1121657 191983056826741081843033 := by
  unfold tailWord_1121657
  simp only [CollatzResearch.WordTrace]
  refine ⟨40910191697435727609539225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27273461131623818406359483 40910191697435727609539225)
  ·
    refine ⟨30682643773076795707154419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40910191697435727609539225 30682643773076795707154419)
    ·
      refine ⟨46023965659615193560731629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30682643773076795707154419 46023965659615193560731629)
      ·
        refine ⟨17258987122355697585274361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46023965659615193560731629 17258987122355697585274361)
        ·
          refine ⟨12944240341766773188955771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17258987122355697585274361 12944240341766773188955771)
          ·
            refine ⟨19416360512650159783433657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12944240341766773188955771 19416360512650159783433657)
            ·
              refine ⟨14562270384487619837575243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19416360512650159783433657 14562270384487619837575243)
              ·
                refine ⟨21843405576731429756362865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14562270384487619837575243 21843405576731429756362865)
                ·
                  refine ⟨16382554182548572317272149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21843405576731429756362865 16382554182548572317272149)
                  ·
                    refine ⟨191983056826741081843033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 16382554182548572317272149 191983056826741081843033)
                    ·
                      rfl

theorem cell23_1121657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 8].length) (baseStart_1121657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1121657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1121657 prefixEnd_1121657 := by exact prefixLift 1121657
  have htrace : WordTrace (prefixWord ++ tailWord_1121657) baseStart_1121657 baseEnd_1121657 := by
    simpa [prefixWord, tailWord_1121657, baseEnd_1121657] using wordTrace_append hprefix tailTrace_1121657
  have hstable : (prefixWord ++ tailWord_1121657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121657).length < 2 ^ (prefixWord ++ tailWord_1121657).sum := by decide
  have hdescent : baseEnd_1121657 < baseStart_1121657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121682 : List Nat := [3, 2, 3, 3, 1, 2, 2, 2, 5]
def baseStart_1121682 : Nat := 118140960795 + 1121682 * 2 ^ 59
def prefixEnd_1121682 : Nat := 4983230072969 + 3 ^ 40 * 1121682 * 2
def baseEnd_1121682 : Nat := 63995778610731738635165

theorem tailTrace_1121682 : CollatzResearch.WordTrace tailWord_1121682 prefixEnd_1121682 63995778610731738635165 := by
  unfold tailWord_1121682
  simp only [CollatzResearch.WordTrace]
  refine ⟨10227775880586289219799825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27274069014896771252799533 10227775880586289219799825)
  ·
    refine ⟨7670831910439716914849869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10227775880586289219799825 7670831910439716914849869)
    ·
      refine ⟨2876561966414893843068701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7670831910439716914849869 2876561966414893843068701)
      ·
        refine ⟨1078710737405585191150763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2876561966414893843068701 1078710737405585191150763)
        ·
          refine ⟨1618066106108377786726145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1078710737405585191150763 1618066106108377786726145)
          ·
            refine ⟨1213549579581283340044609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1618066106108377786726145 1213549579581283340044609)
            ·
              refine ⟨910162184685962505033457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1213549579581283340044609 910162184685962505033457)
              ·
                refine ⟨682621638514471878775093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 910162184685962505033457 682621638514471878775093)
                ·
                  refine ⟨63995778610731738635165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 682621638514471878775093 63995778610731738635165)
                  ·
                    rfl

theorem cell23_1121682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 2, 2, 5].length) (baseStart_1121682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1121682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1121682 prefixEnd_1121682 := by exact prefixLift 1121682
  have htrace : WordTrace (prefixWord ++ tailWord_1121682) baseStart_1121682 baseEnd_1121682 := by
    simpa [prefixWord, tailWord_1121682, baseEnd_1121682] using wordTrace_append hprefix tailTrace_1121682
  have hstable : (prefixWord ++ tailWord_1121682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121682).length < 2 ^ (prefixWord ++ tailWord_1121682).sum := by decide
  have hdescent : baseEnd_1121682 < baseStart_1121682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121698 : List Nat := [3, 3, 1, 2, 1, 3, 1, 1, 2, 4, 2]
def baseStart_1121698 : Nat := 118140960795 + 1121698 * 2 ^ 59
def prefixEnd_1121698 : Nat := 4983230072969 + 3 ^ 40 * 1121698 * 2
def baseEnd_1121698 : Nat := 575970223187057585116411

theorem tailTrace_1121698 : CollatzResearch.WordTrace tailWord_1121698 prefixEnd_1121698 575970223187057585116411 := by
  unfold tailWord_1121698
  simp only [CollatzResearch.WordTrace]
  refine ⟨10227921772571797902945437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27274458060191461074521165 10227921772571797902945437)
  ·
    refine ⟨3835470664714424213604539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10227921772571797902945437 3835470664714424213604539)
    ·
      refine ⟨5753205997071636320406809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3835470664714424213604539 5753205997071636320406809)
      ·
        refine ⟨4314904497803727240305107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5753205997071636320406809 4314904497803727240305107)
        ·
          refine ⟨6472356746705590860457661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4314904497803727240305107 6472356746705590860457661)
          ·
            refine ⟨2427133780014596572671623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6472356746705590860457661 2427133780014596572671623)
            ·
              refine ⟨3640700670021894859007435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2427133780014596572671623 3640700670021894859007435)
              ·
                refine ⟨5461051005032842288511153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3640700670021894859007435 5461051005032842288511153)
                ·
                  refine ⟨4095788253774631716383365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5461051005032842288511153 4095788253774631716383365)
                  ·
                    refine ⟨767960297582743446821881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4095788253774631716383365 767960297582743446821881)
                    ·
                      refine ⟨575970223187057585116411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 767960297582743446821881 575970223187057585116411)
                      ·
                        rfl

theorem cell23_1121698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 2, 4, 2].length) (baseStart_1121698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1121698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1121698 prefixEnd_1121698 := by exact prefixLift 1121698
  have htrace : WordTrace (prefixWord ++ tailWord_1121698) baseStart_1121698 baseEnd_1121698 := by
    simpa [prefixWord, tailWord_1121698, baseEnd_1121698] using wordTrace_append hprefix tailTrace_1121698
  have hstable : (prefixWord ++ tailWord_1121698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121698).length < 2 ^ (prefixWord ++ tailWord_1121698).sum := by decide
  have hdescent : baseEnd_1121698 < baseStart_1121698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121714 : List Nat := [3, 2, 1, 1, 1, 1, 2, 1, 1, 7, 3]
def baseStart_1121714 : Nat := 118140960795 + 1121714 * 2 ^ 59
def prefixEnd_1121714 : Nat := 4983230072969 + 3 ^ 40 * 1121714 * 2
def baseEnd_1121714 : Nat := 575978438877529522516337

theorem tailTrace_1121714 : CollatzResearch.WordTrace tailWord_1121714 prefixEnd_1121714 575978438877529522516337 := by
  unfold tailWord_1121714
  simp only [CollatzResearch.WordTrace]
  refine ⟨10228067664557306586091049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27274847105486150896242797 10228067664557306586091049)
  ·
    refine ⟨7671050748417979939568287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10228067664557306586091049 7671050748417979939568287)
    ·
      refine ⟨11506576122626969909352431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7671050748417979939568287 11506576122626969909352431)
      ·
        refine ⟨17259864183940454864028647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11506576122626969909352431 17259864183940454864028647)
        ·
          refine ⟨25889796275910682296042971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17259864183940454864028647 25889796275910682296042971)
          ·
            refine ⟨38834694413866023444064457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25889796275910682296042971 38834694413866023444064457)
            ·
              refine ⟨29126020810399517583048343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38834694413866023444064457 29126020810399517583048343)
              ·
                refine ⟨43689031215599276374572515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29126020810399517583048343 43689031215599276374572515)
                ·
                  refine ⟨65533546823398914561858773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43689031215599276374572515 65533546823398914561858773)
                  ·
                    refine ⟨1535942503673412060043565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 65533546823398914561858773 1535942503673412060043565)
                    ·
                      refine ⟨575978438877529522516337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1535942503673412060043565 575978438877529522516337)
                      ·
                        rfl

theorem cell23_1121714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 1, 7, 3].length) (baseStart_1121714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1121714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1121714 prefixEnd_1121714 := by exact prefixLift 1121714
  have htrace : WordTrace (prefixWord ++ tailWord_1121714) baseStart_1121714 baseEnd_1121714 := by
    simpa [prefixWord, tailWord_1121714, baseEnd_1121714] using wordTrace_append hprefix tailTrace_1121714
  have hstable : (prefixWord ++ tailWord_1121714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121714).length < 2 ^ (prefixWord ++ tailWord_1121714).sum := by decide
  have hdescent : baseEnd_1121714 < baseStart_1121714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121782 : List Nat := [5, 1, 1, 1, 2, 2, 3, 3, 1, 1, 3]
def baseStart_1121782 : Nat := 118140960795 + 1121782 * 2 ^ 59
def prefixEnd_1121782 : Nat := 4983230072969 + 3 ^ 40 * 1121782 * 2
def baseEnd_1121782 : Nat := 576013355562035256466025

theorem tailTrace_1121782 : CollatzResearch.WordTrace tailWord_1121782 prefixEnd_1121782 576013355562035256466025 := by
  unfold tailWord_1121782
  simp only [CollatzResearch.WordTrace]
  refine ⟨2557171926373929622364975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27276500547988582638559733 2557171926373929622364975)
  ·
    refine ⟨3835757889560894433547463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2557171926373929622364975 3835757889560894433547463)
    ·
      refine ⟨5753636834341341650321195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3835757889560894433547463 5753636834341341650321195)
      ·
        refine ⟨8630455251512012475481793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5753636834341341650321195 8630455251512012475481793)
        ·
          refine ⟨6472841438634009356611345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8630455251512012475481793 6472841438634009356611345)
          ·
            refine ⟨4854631078975507017458509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6472841438634009356611345 4854631078975507017458509)
            ·
              refine ⟨1820486654615815131546941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4854631078975507017458509 1820486654615815131546941)
              ·
                refine ⟨682682495480930674330103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1820486654615815131546941 682682495480930674330103)
                ·
                  refine ⟨1024023743221396011495155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 682682495480930674330103 1024023743221396011495155)
                  ·
                    refine ⟨1536035614832094017242733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1024023743221396011495155 1536035614832094017242733)
                    ·
                      refine ⟨576013355562035256466025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1536035614832094017242733 576013355562035256466025)
                      ·
                        rfl

theorem cell23_1121782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 3, 1, 1, 3].length) (baseStart_1121782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1121782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1121782 prefixEnd_1121782 := by exact prefixLift 1121782
  have htrace : WordTrace (prefixWord ++ tailWord_1121782) baseStart_1121782 baseEnd_1121782 := by
    simpa [prefixWord, tailWord_1121782, baseEnd_1121782] using wordTrace_append hprefix tailTrace_1121782
  have hstable : (prefixWord ++ tailWord_1121782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121782).length < 2 ^ (prefixWord ++ tailWord_1121782).sum := by decide
  have hdescent : baseEnd_1121782 < baseStart_1121782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121788 : List Nat := [2, 2, 2, 1, 2, 1, 2, 2, 5, 2, 2]
def baseStart_1121788 : Nat := 118140960795 + 1121788 * 2 ^ 59
def prefixEnd_1121788 : Nat := 4983230072969 + 3 ^ 40 * 1121788 * 2
def baseEnd_1121788 : Nat := 576016436445962232990997

theorem tailTrace_1121788 : CollatzResearch.WordTrace tailWord_1121788 prefixEnd_1121788 576016436445962232990997 := by
  unfold tailWord_1121788
  simp only [CollatzResearch.WordTrace]
  refine ⟨20457484829980568491279009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27276646439974091321705345 20457484829980568491279009)
  ·
    refine ⟨15343113622485426368459257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20457484829980568491279009 15343113622485426368459257)
    ·
      refine ⟨11507335216864069776344443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15343113622485426368459257 11507335216864069776344443)
      ·
        refine ⟨17261002825296104664516665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11507335216864069776344443 17261002825296104664516665)
        ·
          refine ⟨12945752118972078498387499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17261002825296104664516665 12945752118972078498387499)
          ·
            refine ⟨19418628178458117747581249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12945752118972078498387499 19418628178458117747581249)
            ·
              refine ⟨14563971133843588310685937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19418628178458117747581249 14563971133843588310685937)
              ·
                refine ⟨10922978350382691233014453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14563971133843588310685937 10922978350382691233014453)
                ·
                  refine ⟨1024029220348377303095105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10922978350382691233014453 1024029220348377303095105)
                  ·
                    refine ⟨768021915261282977321329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1024029220348377303095105 768021915261282977321329)
                    ·
                      refine ⟨576016436445962232990997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 768021915261282977321329 576016436445962232990997)
                      ·
                        rfl

theorem cell23_1121788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 5, 2, 2].length) (baseStart_1121788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1121788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1121788 prefixEnd_1121788 := by exact prefixLift 1121788
  have htrace : WordTrace (prefixWord ++ tailWord_1121788) baseStart_1121788 baseEnd_1121788 := by
    simpa [prefixWord, tailWord_1121788, baseEnd_1121788] using wordTrace_append hprefix tailTrace_1121788
  have hstable : (prefixWord ++ tailWord_1121788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121788).length < 2 ^ (prefixWord ++ tailWord_1121788).sum := by decide
  have hdescent : baseEnd_1121788 < baseStart_1121788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121825 : List Nat := [1, 2, 3, 2, 2, 4, 1, 2, 1, 2, 3]
def baseStart_1121825 : Nat := 118140960795 + 1121825 * 2 ^ 59
def prefixEnd_1121825 : Nat := 4983230072969 + 3 ^ 40 * 1121825 * 2
def baseEnd_1121825 : Nat := 576035435230178588228327

theorem tailTrace_1121825 : CollatzResearch.WordTrace tailWord_1121825 prefixEnd_1121825 576035435230178588228327 := by
  unfold tailWord_1121825
  simp only [CollatzResearch.WordTrace]
  refine ⟨40916319160827092301654929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27277546107218061534436619 40916319160827092301654929)
  ·
    refine ⟨30687239370620319226241197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40916319160827092301654929 30687239370620319226241197)
    ·
      refine ⟨11507714763982619709840449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30687239370620319226241197 11507714763982619709840449)
      ·
        refine ⟨8630786072986964782380337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11507714763982619709840449 8630786072986964782380337)
        ·
          refine ⟨6473089554740223586785253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8630786072986964782380337 6473089554740223586785253)
          ·
            refine ⟨1213704291513791922522235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6473089554740223586785253 1213704291513791922522235)
            ·
              refine ⟨1820556437270687883783353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1213704291513791922522235 1820556437270687883783353)
              ·
                refine ⟨1365417327953015912837515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1820556437270687883783353 1365417327953015912837515)
                ·
                  refine ⟨2048125991929523869256273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1365417327953015912837515 2048125991929523869256273)
                  ·
                    refine ⟨1536094493947142901942205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2048125991929523869256273 1536094493947142901942205)
                    ·
                      refine ⟨576035435230178588228327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1536094493947142901942205 576035435230178588228327)
                      ·
                        rfl

theorem cell23_1121825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 2, 1, 2, 3].length) (baseStart_1121825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1121825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1121825 prefixEnd_1121825 := by exact prefixLift 1121825
  have htrace : WordTrace (prefixWord ++ tailWord_1121825) baseStart_1121825 baseEnd_1121825 := by
    simpa [prefixWord, tailWord_1121825, baseEnd_1121825] using wordTrace_append hprefix tailTrace_1121825
  have hstable : (prefixWord ++ tailWord_1121825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121825).length < 2 ^ (prefixWord ++ tailWord_1121825).sum := by decide
  have hdescent : baseEnd_1121825 < baseStart_1121825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121838 : List Nat := [4, 1, 3, 1, 2, 1, 1, 1, 3, 3, 3]
def baseStart_1121838 : Nat := 118140960795 + 1121838 * 2 ^ 59
def prefixEnd_1121838 : Nat := 4983230072969 + 3 ^ 40 * 1121838 * 2
def baseEnd_1121838 : Nat := 576042110478687037365767

theorem tailTrace_1121838 : CollatzResearch.WordTrace tailWord_1121838 prefixEnd_1121838 576042110478687037365767 := by
  unfold tailWord_1121838
  simp only [CollatzResearch.WordTrace]
  refine ⟨5114599163722499440234771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27277862206519997014585445 5114599163722499440234771)
  ·
    refine ⟨7671898745583749160352157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5114599163722499440234771 7671898745583749160352157)
    ·
      refine ⟨2876962029593905935132059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7671898745583749160352157 2876962029593905935132059)
      ·
        refine ⟨4315443044390858902698089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2876962029593905935132059 4315443044390858902698089)
        ·
          refine ⟨3236582283293144177023567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4315443044390858902698089 3236582283293144177023567)
          ·
            refine ⟨4854873424939716265535351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3236582283293144177023567 4854873424939716265535351)
            ·
              refine ⟨7282310137409574398303027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4854873424939716265535351 7282310137409574398303027)
              ·
                refine ⟨10923465206114361597454541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7282310137409574398303027 10923465206114361597454541)
                ·
                  refine ⟨4096299452292885599045453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10923465206114361597454541 4096299452292885599045453)
                  ·
                    refine ⟨1536112294609832099642045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4096299452292885599045453 1536112294609832099642045)
                    ·
                      refine ⟨576042110478687037365767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1536112294609832099642045 576042110478687037365767)
                      ·
                        rfl

theorem cell23_1121838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_1121838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1121838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1121838 prefixEnd_1121838 := by exact prefixLift 1121838
  have htrace : WordTrace (prefixWord ++ tailWord_1121838) baseStart_1121838 baseEnd_1121838 := by
    simpa [prefixWord, tailWord_1121838, baseEnd_1121838] using wordTrace_append hprefix tailTrace_1121838
  have hstable : (prefixWord ++ tailWord_1121838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121838).length < 2 ^ (prefixWord ++ tailWord_1121838).sum := by decide
  have hdescent : baseEnd_1121838 < baseStart_1121838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121855 : List Nat := [1, 1, 2, 2, 3, 4, 2, 2, 2, 1, 3]
def baseStart_1121855 : Nat := 118140960795 + 1121855 * 2 ^ 59
def prefixEnd_1121855 : Nat := 4983230072969 + 3 ^ 40 * 1121855 * 2
def baseEnd_1121855 : Nat := 576050839649813470853189

theorem tailTrace_1121855 : CollatzResearch.WordTrace tailWord_1121855 prefixEnd_1121855 576050839649813470853189 := by
  unfold tailWord_1121855
  simp only [CollatzResearch.WordTrace]
  refine ⟨40917413350718407425247019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27278275567145604950164679 40917413350718407425247019)
  ·
    refine ⟨61376120026077611137870529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40917413350718407425247019 61376120026077611137870529)
    ·
      refine ⟨46032090019558208353402897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61376120026077611137870529 46032090019558208353402897)
      ·
        refine ⟨34524067514668656265052173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46032090019558208353402897 34524067514668656265052173)
        ·
          refine ⟨12946525318000746099394565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34524067514668656265052173 12946525318000746099394565)
          ·
            refine ⟨2427473497125139893636481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12946525318000746099394565 2427473497125139893636481)
            ·
              refine ⟨1820605122843854920227361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2427473497125139893636481 1820605122843854920227361)
              ·
                refine ⟨1365453842132891190170521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1820605122843854920227361 1365453842132891190170521)
                ·
                  refine ⟨1024090381599668392627891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1365453842132891190170521 1024090381599668392627891)
                  ·
                    refine ⟨1536135572399502588941837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1024090381599668392627891 1536135572399502588941837)
                    ·
                      refine ⟨576050839649813470853189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1536135572399502588941837 576050839649813470853189)
                      ·
                        rfl

theorem cell23_1121855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 2, 2, 1, 3].length) (baseStart_1121855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1121855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1121855 prefixEnd_1121855 := by exact prefixLift 1121855
  have htrace : WordTrace (prefixWord ++ tailWord_1121855) baseStart_1121855 baseEnd_1121855 := by
    simpa [prefixWord, tailWord_1121855, baseEnd_1121855] using wordTrace_append hprefix tailTrace_1121855
  have hstable : (prefixWord ++ tailWord_1121855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121855).length < 2 ^ (prefixWord ++ tailWord_1121855).sum := by decide
  have hdescent : baseEnd_1121855 < baseStart_1121855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121862 : List Nat := [6, 1, 1, 1, 4, 1, 1, 8]
def baseStart_1121862 : Nat := 118140960795 + 1121862 * 2 ^ 59
def prefixEnd_1121862 : Nat := 4983230072969 + 3 ^ 40 * 1121862 * 2
def baseEnd_1121862 : Nat := 21335349407940553461691

theorem tailTrace_1121862 : CollatzResearch.WordTrace tailWord_1121862 prefixEnd_1121862 21335349407940553461691 := by
  unfold tailWord_1121862
  simp only [CollatzResearch.WordTrace]
  refine ⟨1278677145677907738148495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 27278445774462031747167893 1278677145677907738148495)
  ·
    refine ⟨1918015718516861607222743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1278677145677907738148495 1918015718516861607222743)
    ·
      refine ⟨2877023577775292410834115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1918015718516861607222743 2877023577775292410834115)
      ·
        refine ⟨4315535366662938616251173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2877023577775292410834115 4315535366662938616251173)
        ·
          refine ⟨809162881249300990547095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4315535366662938616251173 809162881249300990547095)
          ·
            refine ⟨1213744321873951485820643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 809162881249300990547095 1213744321873951485820643)
            ·
              refine ⟨1820616482810927228730965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1213744321873951485820643 1820616482810927228730965)
              ·
                refine ⟨21335349407940553461691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1820616482810927228730965 21335349407940553461691)
                ·
                  rfl

theorem cell23_1121862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 8].length) (baseStart_1121862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1121862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1121862 prefixEnd_1121862 := by exact prefixLift 1121862
  have htrace : WordTrace (prefixWord ++ tailWord_1121862) baseStart_1121862 baseEnd_1121862 := by
    simpa [prefixWord, tailWord_1121862, baseEnd_1121862] using wordTrace_append hprefix tailTrace_1121862
  have hstable : (prefixWord ++ tailWord_1121862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121862).length < 2 ^ (prefixWord ++ tailWord_1121862).sum := by decide
  have hdescent : baseEnd_1121862 < baseStart_1121862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121968 : List Nat := [2, 1, 1, 1, 2, 1, 4, 1, 4, 4, 2]
def baseStart_1121968 : Nat := 118140960795 + 1121968 * 2 ^ 59
def prefixEnd_1121968 : Nat := 4983230072969 + 3 ^ 40 * 1121968 * 2
def baseEnd_1121968 : Nat := 576108862963771528740169

theorem tailTrace_1121968 : CollatzResearch.WordTrace tailWord_1121968 prefixEnd_1121968 576108862963771528740169 := by
  unfold tailWord_1121968
  simp only [CollatzResearch.WordTrace]
  refine ⟨20460767399654513862055279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27281023199539351816073705 20460767399654513862055279)
  ·
    refine ⟨30691151099481770793082919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20460767399654513862055279 30691151099481770793082919)
    ·
      refine ⟨46036726649222656189624379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30691151099481770793082919 46036726649222656189624379)
      ·
        refine ⟨69055089973833984284436569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46036726649222656189624379 69055089973833984284436569)
        ·
          refine ⟨51791317480375488213327427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69055089973833984284436569 51791317480375488213327427)
          ·
            refine ⟨77686976220563232319991141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51791317480375488213327427 77686976220563232319991141)
            ·
              refine ⟨14566308041355606059998339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77686976220563232319991141 14566308041355606059998339)
              ·
                refine ⟨21849462062033409089997509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14566308041355606059998339 21849462062033409089997509)
                ·
                  refine ⟨4096774136631264204374533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21849462062033409089997509 4096774136631264204374533)
                  ·
                    refine ⟨768145150618362038320225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4096774136631264204374533 768145150618362038320225)
                    ·
                      refine ⟨576108862963771528740169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 768145150618362038320225 576108862963771528740169)
                      ·
                        rfl

theorem cell23_1121968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 4, 4, 2].length) (baseStart_1121968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1121968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1121968 prefixEnd_1121968 := by exact prefixLift 1121968
  have htrace : WordTrace (prefixWord ++ tailWord_1121968) baseStart_1121968 baseEnd_1121968 := by
    simpa [prefixWord, tailWord_1121968, baseEnd_1121968] using wordTrace_append hprefix tailTrace_1121968
  have hstable : (prefixWord ++ tailWord_1121968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121968).length < 2 ^ (prefixWord ++ tailWord_1121968).sum := by decide
  have hdescent : baseEnd_1121968 < baseStart_1121968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122029 : List Nat := [1, 5, 1, 2, 1, 2, 4, 2, 1, 4]
def baseStart_1122029 : Nat := 118140960795 + 1122029 * 2 ^ 59
def prefixEnd_1122029 : Nat := 4983230072969 + 3 ^ 40 * 1122029 * 2
def baseEnd_1122029 : Nat := 192046728427898596692463

theorem tailTrace_1122029 : CollatzResearch.WordTrace tailWord_1122029 prefixEnd_1122029 192046728427898596692463 := by
  unfold tailWord_1122029
  simp only [CollatzResearch.WordTrace]
  refine ⟨40923759652088035142081141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27282506434725356761387427 40923759652088035142081141)
  ·
    refine ⟨3836602467383253294570107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40923759652088035142081141 3836602467383253294570107)
    ·
      refine ⟨5754903701074879941855161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3836602467383253294570107 5754903701074879941855161)
      ·
        refine ⟨4316177775806159956391371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5754903701074879941855161 4316177775806159956391371)
        ·
          refine ⟨6474266663709239934587057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4316177775806159956391371 6474266663709239934587057)
          ·
            refine ⟨4855699997781929950940293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6474266663709239934587057 4855699997781929950940293)
            ·
              refine ⟨910443749584111865801305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4855699997781929950940293 910443749584111865801305)
              ·
                refine ⟨682832812188083899350979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 910443749584111865801305 682832812188083899350979)
                ·
                  refine ⟨1024249218282125849026469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 682832812188083899350979 1024249218282125849026469)
                  ·
                    refine ⟨192046728427898596692463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1024249218282125849026469 192046728427898596692463)
                    ·
                      rfl

theorem cell23_1122029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 4, 2, 1, 4].length) (baseStart_1122029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1122029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1122029 prefixEnd_1122029 := by exact prefixLift 1122029
  have htrace : WordTrace (prefixWord ++ tailWord_1122029) baseStart_1122029 baseEnd_1122029 := by
    simpa [prefixWord, tailWord_1122029, baseEnd_1122029] using wordTrace_append hprefix tailTrace_1122029
  have hstable : (prefixWord ++ tailWord_1122029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122029).length < 2 ^ (prefixWord ++ tailWord_1122029).sum := by decide
  have hdescent : baseEnd_1122029 < baseStart_1122029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122052 : List Nat := [2, 3, 2, 2, 1, 3, 1, 2, 3, 1, 3]
def baseStart_1122052 : Nat := 118140960795 + 1122052 * 2 ^ 59
def prefixEnd_1122052 : Nat := 4983230072969 + 3 ^ 40 * 1122052 * 2
def baseEnd_1122052 : Nat := 576151995338749200089783

theorem tailTrace_1122052 : CollatzResearch.WordTrace tailWord_1122052 prefixEnd_1122052 576151995338749200089783 := by
  unfold tailWord_1122052
  simp only [CollatzResearch.WordTrace]
  refine ⟨20462299265502355035084205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27283065687336473380112273 20462299265502355035084205)
  ·
    refine ⟨7673362224563383138156577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20462299265502355035084205 7673362224563383138156577)
    ·
      refine ⟨5755021668422537353617433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7673362224563383138156577 5755021668422537353617433)
      ·
        refine ⟨4316266251316903015213075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5755021668422537353617433 4316266251316903015213075)
        ·
          refine ⟨6474399376975354522819613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4316266251316903015213075 6474399376975354522819613)
          ·
            refine ⟨2427899766365757946057355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6474399376975354522819613 2427899766365757946057355)
            ·
              refine ⟨3641849649548636919086033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2427899766365757946057355 3641849649548636919086033)
              ·
                refine ⟨2731387237161477689314525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3641849649548636919086033 2731387237161477689314525)
                ·
                  refine ⟨1024270213935554133492947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2731387237161477689314525 1024270213935554133492947)
                  ·
                    refine ⟨1536405320903331200239421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1024270213935554133492947 1536405320903331200239421)
                    ·
                      refine ⟨576151995338749200089783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1536405320903331200239421 576151995338749200089783)
                      ·
                        rfl

theorem cell23_1122052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_1122052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1122052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1122052 prefixEnd_1122052 := by exact prefixLift 1122052
  have htrace : WordTrace (prefixWord ++ tailWord_1122052) baseStart_1122052 baseEnd_1122052 := by
    simpa [prefixWord, tailWord_1122052, baseEnd_1122052] using wordTrace_append hprefix tailTrace_1122052
  have hstable : (prefixWord ++ tailWord_1122052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122052).length < 2 ^ (prefixWord ++ tailWord_1122052).sum := by decide
  have hdescent : baseEnd_1122052 < baseStart_1122052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122062 : List Nat := [4, 1, 1, 2, 1, 1, 5, 1, 2, 3, 2]
def baseStart_1122062 : Nat := 118140960795 + 1122062 * 2 ^ 59
def prefixEnd_1122062 : Nat := 4983230072969 + 3 ^ 40 * 1122062 * 2
def baseEnd_1122062 : Nat := 576157130145294160964737

theorem tailTrace_1122062 : CollatzResearch.WordTrace tailWord_1122062 prefixEnd_1122062 576157130145294160964737 := by
  unfold tailWord_1122062
  simp only [CollatzResearch.WordTrace]
  refine ⟨5115620407621060222254055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27283308840645654518688293 5115620407621060222254055)
  ·
    refine ⟨7673430611431590333381083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5115620407621060222254055 7673430611431590333381083)
    ·
      refine ⟨11510145917147385500071625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7673430611431590333381083 11510145917147385500071625)
      ·
        refine ⟨8632609437860539125053719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11510145917147385500071625 8632609437860539125053719)
        ·
          refine ⟨12948914156790808687580579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8632609437860539125053719 12948914156790808687580579)
          ·
            refine ⟨19423371235186213031370869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12948914156790808687580579 19423371235186213031370869)
            ·
              refine ⟨1820941053298707471691019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19423371235186213031370869 1820941053298707471691019)
              ·
                refine ⟨2731411579948061207536529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1820941053298707471691019 2731411579948061207536529)
                ·
                  refine ⟨2048558684961045905652397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2731411579948061207536529 2048558684961045905652397)
                  ·
                    refine ⟨768209506860392214619649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2048558684961045905652397 768209506860392214619649)
                    ·
                      refine ⟨576157130145294160964737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 768209506860392214619649 576157130145294160964737)
                      ·
                        rfl

theorem cell23_1122062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 1, 2, 3, 2].length) (baseStart_1122062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1122062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1122062 prefixEnd_1122062 := by exact prefixLift 1122062
  have htrace : WordTrace (prefixWord ++ tailWord_1122062) baseStart_1122062 baseEnd_1122062 := by
    simpa [prefixWord, tailWord_1122062, baseEnd_1122062] using wordTrace_append hprefix tailTrace_1122062
  have hstable : (prefixWord ++ tailWord_1122062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122062).length < 2 ^ (prefixWord ++ tailWord_1122062).sum := by decide
  have hdescent : baseEnd_1122062 < baseStart_1122062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122069 : List Nat := [1, 3, 2, 1, 2, 4, 2, 3, 1, 1, 3]
def baseStart_1122069 : Nat := 118140960795 + 1122069 * 2 ^ 59
def prefixEnd_1122069 : Nat := 4983230072969 + 3 ^ 40 * 1122069 * 2
def baseEnd_1122069 : Nat := 576160724509875633577205

theorem tailTrace_1122069 : CollatzResearch.WordTrace tailWord_1122069 prefixEnd_1122069 576160724509875633577205 := by
  unfold tailWord_1122069
  simp only [CollatzResearch.WordTrace]
  refine ⟨40925218571943121973537261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27283479047962081315691507 40925218571943121973537261)
  ·
    refine ⟨15346956964478670740076473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40925218571943121973537261 15346956964478670740076473)
    ·
      refine ⟨11510217723359003055057355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15346956964478670740076473 11510217723359003055057355)
      ·
        refine ⟨17265326585038504582586033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11510217723359003055057355 17265326585038504582586033)
        ·
          refine ⟨12948994938778878436939525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17265326585038504582586033 12948994938778878436939525)
          ·
            refine ⟨2427936551021039706926161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12948994938778878436939525 2427936551021039706926161)
            ·
              refine ⟨1820952413265779780194621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2427936551021039706926161 1820952413265779780194621)
              ·
                refine ⟨682857154974667417572983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1820952413265779780194621 682857154974667417572983)
                ·
                  refine ⟨1024285732462001126359475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 682857154974667417572983 1024285732462001126359475)
                  ·
                    refine ⟨1536428598693001689539213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1024285732462001126359475 1536428598693001689539213)
                    ·
                      refine ⟨576160724509875633577205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1536428598693001689539213 576160724509875633577205)
                      ·
                        rfl

theorem cell23_1122069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 3, 1, 1, 3].length) (baseStart_1122069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1122069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1122069 prefixEnd_1122069 := by exact prefixLift 1122069
  have htrace : WordTrace (prefixWord ++ tailWord_1122069) baseStart_1122069 baseEnd_1122069 := by
    simpa [prefixWord, tailWord_1122069, baseEnd_1122069] using wordTrace_append hprefix tailTrace_1122069
  have hstable : (prefixWord ++ tailWord_1122069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122069).length < 2 ^ (prefixWord ++ tailWord_1122069).sum := by decide
  have hdescent : baseEnd_1122069 < baseStart_1122069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122085 : List Nat := [1, 3, 1, 2, 3, 3, 1, 1, 4, 4]
def baseStart_1122085 : Nat := 118140960795 + 1122085 * 2 ^ 59
def prefixEnd_1122085 : Nat := 4983230072969 + 3 ^ 40 * 1122085 * 2
def baseEnd_1122085 : Nat := 192056313400115856992377

theorem tailTrace_1122085 : CollatzResearch.WordTrace tailWord_1122085 prefixEnd_1122085 192056313400115856992377 := by
  unfold tailWord_1122085
  simp only [CollatzResearch.WordTrace]
  refine ⟨40925802139885156706119709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27283868093256771137413139 40925802139885156706119709)
  ·
    refine ⟨15347175802456933764794891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40925802139885156706119709 15347175802456933764794891)
    ·
      refine ⟨23020763703685400647192337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15347175802456933764794891 23020763703685400647192337)
      ·
        refine ⟨17265572777764050485394253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23020763703685400647192337 17265572777764050485394253)
        ·
          refine ⟨6474589791661518932022845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17265572777764050485394253 6474589791661518932022845)
          ·
            refine ⟨2427971171873069599508567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6474589791661518932022845 2427971171873069599508567)
            ·
              refine ⟨3641956757809604399262851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2427971171873069599508567 3641956757809604399262851)
              ·
                refine ⟨5462935136714406598894277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3641956757809604399262851 5462935136714406598894277)
                ·
                  refine ⟨1024300338133951237292677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5462935136714406598894277 1024300338133951237292677)
                  ·
                    refine ⟨192056313400115856992377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1024300338133951237292677 192056313400115856992377)
                    ·
                      rfl

theorem cell23_1122085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 4, 4].length) (baseStart_1122085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1122085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1122085 prefixEnd_1122085 := by exact prefixLift 1122085
  have htrace : WordTrace (prefixWord ++ tailWord_1122085) baseStart_1122085 baseEnd_1122085 := by
    simpa [prefixWord, tailWord_1122085, baseEnd_1122085] using wordTrace_append hprefix tailTrace_1122085
  have hstable : (prefixWord ++ tailWord_1122085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122085).length < 2 ^ (prefixWord ++ tailWord_1122085).sum := by decide
  have hdescent : baseEnd_1122085 < baseStart_1122085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122092 : List Nat := [2, 2, 1, 1, 1, 5, 1, 3, 3, 2, 2]
def baseStart_1122092 : Nat := 118140960795 + 1122092 * 2 ^ 59
def prefixEnd_1122092 : Nat := 4983230072969 + 3 ^ 40 * 1122092 * 2
def baseEnd_1122092 : Nat := 576172534564929043589599

theorem tailTrace_1122092 : CollatzResearch.WordTrace tailWord_1122092 prefixEnd_1122092 576172534564929043589599 := by
  unfold tailWord_1122092
  simp only [CollatzResearch.WordTrace]
  refine ⟨20463028725429898450812265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27284038300573197934416353 20463028725429898450812265)
  ·
    refine ⟨15347271544072423838109199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20463028725429898450812265 15347271544072423838109199)
    ·
      refine ⟨23020907316108635757163799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15347271544072423838109199 23020907316108635757163799)
      ·
        refine ⟨34531360974162953635745699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23020907316108635757163799 34531360974162953635745699)
        ·
          refine ⟨51797041461244430453618549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34531360974162953635745699 51797041461244430453618549)
          ·
            refine ⟨4855972636991665355026739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51797041461244430453618549 4855972636991665355026739)
            ·
              refine ⟨7283958955487498032540109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4855972636991665355026739 7283958955487498032540109)
              ·
                refine ⟨2731484608307811762202541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7283958955487498032540109 2731484608307811762202541)
                ·
                  refine ⟨1024306728115429410825953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2731484608307811762202541 1024306728115429410825953)
                  ·
                    refine ⟨768230046086572058119465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1024306728115429410825953 768230046086572058119465)
                    ·
                      refine ⟨576172534564929043589599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 768230046086572058119465 576172534564929043589599)
                      ·
                        rfl

theorem cell23_1122092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 2, 2].length) (baseStart_1122092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1122092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1122092 prefixEnd_1122092 := by exact prefixLift 1122092
  have htrace : WordTrace (prefixWord ++ tailWord_1122092) baseStart_1122092 baseEnd_1122092 := by
    simpa [prefixWord, tailWord_1122092, baseEnd_1122092] using wordTrace_append hprefix tailTrace_1122092
  have hstable : (prefixWord ++ tailWord_1122092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122092).length < 2 ^ (prefixWord ++ tailWord_1122092).sum := by decide
  have hdescent : baseEnd_1122092 < baseStart_1122092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122102 : List Nat := [5, 1, 2, 2, 1, 1, 3, 1, 1, 6]
def baseStart_1122102 : Nat := 118140960795 + 1122102 * 2 ^ 59
def prefixEnd_1122102 : Nat := 4983230072969 + 3 ^ 40 * 1122102 * 2
def baseEnd_1122102 : Nat := 192059223123824668154851

theorem tailTrace_1122102 : CollatzResearch.WordTrace tailWord_1122102 prefixEnd_1122102 192059223123824668154851 := by
  unfold tailWord_1122102
  simp only [CollatzResearch.WordTrace]
  refine ⟨2557901386301473038093035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27284281453882379072992373 2557901386301473038093035)
  ·
    refine ⟨3836852079452209557139553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2557901386301473038093035 3836852079452209557139553)
    ·
      refine ⟨2877639059589157167854665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3836852079452209557139553 2877639059589157167854665)
      ·
        refine ⟨2158229294691867875890999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2877639059589157167854665 2158229294691867875890999)
        ·
          refine ⟨3237343942037801813836499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2158229294691867875890999 3237343942037801813836499)
          ·
            refine ⟨4856015913056702720754749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3237343942037801813836499 4856015913056702720754749)
            ·
              refine ⟨1821005967396263520283031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4856015913056702720754749 1821005967396263520283031)
              ·
                refine ⟨2731508951094395280424547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1821005967396263520283031 2731508951094395280424547)
                ·
                  refine ⟨4097263426641592920636821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2731508951094395280424547 4097263426641592920636821)
                  ·
                    refine ⟨192059223123824668154851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4097263426641592920636821 192059223123824668154851)
                    ·
                      rfl

theorem cell23_1122102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_1122102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1122102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1122102 prefixEnd_1122102 := by exact prefixLift 1122102
  have htrace : WordTrace (prefixWord ++ tailWord_1122102) baseStart_1122102 baseEnd_1122102 := by
    simpa [prefixWord, tailWord_1122102, baseEnd_1122102] using wordTrace_append hprefix tailTrace_1122102
  have hstable : (prefixWord ++ tailWord_1122102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122102).length < 2 ^ (prefixWord ++ tailWord_1122102).sum := by decide
  have hdescent : baseEnd_1122102 < baseStart_1122102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122109 : List Nat := [1, 4, 1, 4, 1, 1, 2, 2, 3, 2, 2]
def baseStart_1122109 : Nat := 118140960795 + 1122109 * 2 ^ 59
def prefixEnd_1122109 : Nat := 4983230072969 + 3 ^ 40 * 1122109 * 2
def baseEnd_1122109 : Nat := 576181263736055477077021

theorem tailTrace_1122109 : CollatzResearch.WordTrace tailWord_1122109 prefixEnd_1122109 576181263736055477077021 := by
  unfold tailWord_1122109
  simp only [CollatzResearch.WordTrace]
  refine ⟨40926677491798208804993381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27284451661198805869995587 40926677491798208804993381)
  ·
    refine ⟨7673752029712164150936259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40926677491798208804993381 7673752029712164150936259)
    ·
      refine ⟨11510628044568246226404389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7673752029712164150936259 11510628044568246226404389)
      ·
        refine ⟨2158242758356546167450823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11510628044568246226404389 2158242758356546167450823)
        ·
          refine ⟨3237364137534819251176235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2158242758356546167450823 3237364137534819251176235)
          ·
            refine ⟨4856046206302228876764353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3237364137534819251176235 4856046206302228876764353)
            ·
              refine ⟨3642034654726671657573265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4856046206302228876764353 3642034654726671657573265)
              ·
                refine ⟨2731525991045003743179949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3642034654726671657573265 2731525991045003743179949)
                ·
                  refine ⟨1024322246641876403692481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2731525991045003743179949 1024322246641876403692481)
                  ·
                    refine ⟨768241684981407302769361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1024322246641876403692481 768241684981407302769361)
                    ·
                      refine ⟨576181263736055477077021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 768241684981407302769361 576181263736055477077021)
                      ·
                        rfl

theorem cell23_1122109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_1122109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1122109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1122109 prefixEnd_1122109 := by exact prefixLift 1122109
  have htrace : WordTrace (prefixWord ++ tailWord_1122109) baseStart_1122109 baseEnd_1122109 := by
    simpa [prefixWord, tailWord_1122109, baseEnd_1122109] using wordTrace_append hprefix tailTrace_1122109
  have hstable : (prefixWord ++ tailWord_1122109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122109).length < 2 ^ (prefixWord ++ tailWord_1122109).sum := by decide
  have hdescent : baseEnd_1122109 < baseStart_1122109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122115 : List Nat := [1, 1, 1, 3, 1, 7, 2, 7]
def baseStart_1122115 : Nat := 118140960795 + 1122115 * 2 ^ 59
def prefixEnd_1122115 : Nat := 4983230072969 + 3 ^ 40 * 1122115 * 2
def baseEnd_1122115 : Nat := 21340160911851201985259

theorem tailTrace_1122115 : CollatzResearch.WordTrace tailWord_1122115 prefixEnd_1122115 21340160911851201985259 := by
  unfold tailWord_1122115
  simp only [CollatzResearch.WordTrace]
  refine ⟨40926896329776471829711799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27284597553184314553141199 40926896329776471829711799)
  ·
    refine ⟨61390344494664707744567699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40926896329776471829711799 61390344494664707744567699)
    ·
      refine ⟨92085516741997061616851549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61390344494664707744567699 92085516741997061616851549)
      ·
        refine ⟨34532068778248898106319331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92085516741997061616851549 34532068778248898106319331)
        ·
          refine ⟨51798103167373347159478997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34532068778248898106319331 51798103167373347159478997)
          ·
            refine ⟨1214018042985312824050289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 51798103167373347159478997 1214018042985312824050289)
            ·
              refine ⟨910513532238984618037717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1214018042985312824050289 910513532238984618037717)
              ·
                refine ⟨21340160911851201985259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 910513532238984618037717 21340160911851201985259)
                ·
                  rfl

theorem cell23_1122115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 2, 7].length) (baseStart_1122115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1122115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1122115 prefixEnd_1122115 := by exact prefixLift 1122115
  have htrace : WordTrace (prefixWord ++ tailWord_1122115) baseStart_1122115 baseEnd_1122115 := by
    simpa [prefixWord, tailWord_1122115, baseEnd_1122115] using wordTrace_append hprefix tailTrace_1122115
  have hstable : (prefixWord ++ tailWord_1122115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122115).length < 2 ^ (prefixWord ++ tailWord_1122115).sum := by decide
  have hdescent : baseEnd_1122115 < baseStart_1122115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122138 : List Nat := [3, 1, 1, 2, 1, 3, 1, 2, 2, 2, 5]
def baseStart_1122138 : Nat := 118140960795 + 1122138 * 2 ^ 59
def prefixEnd_1122138 : Nat := 4983230072969 + 3 ^ 40 * 1122138 * 2
def baseEnd_1122138 : Nat := 576196154675035863614387

theorem tailTrace_1122138 : CollatzResearch.WordTrace tailWord_1122138 prefixEnd_1122138 576196154675035863614387 := by
  unfold tailWord_1122138
  simp only [CollatzResearch.WordTrace]
  refine ⟨10231933802173286689449767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27285156805795431171866045 10231933802173286689449767)
  ·
    refine ⟨15347900703259930034174651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10231933802173286689449767 15347900703259930034174651)
    ·
      refine ⟨23021851054889895051261977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15347900703259930034174651 23021851054889895051261977)
      ·
        refine ⟨17266388291167421288446483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23021851054889895051261977 17266388291167421288446483)
        ·
          refine ⟨25899582436751131932669725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17266388291167421288446483 25899582436751131932669725)
          ·
            refine ⟨9712343413781674474751147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25899582436751131932669725 9712343413781674474751147)
            ·
              refine ⟨14568515120672511712126721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9712343413781674474751147 14568515120672511712126721)
              ·
                refine ⟨10926386340504383784095041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14568515120672511712126721 10926386340504383784095041)
                ·
                  refine ⟨8194789755378287838071281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10926386340504383784095041 8194789755378287838071281)
                  ·
                    refine ⟨6146092316533715878553461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8194789755378287838071281 6146092316533715878553461)
                    ·
                      refine ⟨576196154675035863614387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6146092316533715878553461 576196154675035863614387)
                      ·
                        rfl

theorem cell23_1122138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 2, 2, 5].length) (baseStart_1122138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1122138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1122138 prefixEnd_1122138 := by exact prefixLift 1122138
  have htrace : WordTrace (prefixWord ++ tailWord_1122138) baseStart_1122138 baseEnd_1122138 := by
    simpa [prefixWord, tailWord_1122138, baseEnd_1122138] using wordTrace_append hprefix tailTrace_1122138
  have hstable : (prefixWord ++ tailWord_1122138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122138).length < 2 ^ (prefixWord ++ tailWord_1122138).sum := by decide
  have hdescent : baseEnd_1122138 < baseStart_1122138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122152 : List Nat := [2, 1, 4, 2, 1, 1, 2, 2, 3, 3, 2]
def baseStart_1122152 : Nat := 118140960795 + 1122152 * 2 ^ 59
def prefixEnd_1122152 : Nat := 4983230072969 + 3 ^ 40 * 1122152 * 2
def baseEnd_1122152 : Nat := 576203343404198808839323

theorem tailTrace_1122152 : CollatzResearch.WordTrace tailWord_1122152 prefixEnd_1122152 576203343404198808839323 := by
  unfold tailWord_1122152
  simp only [CollatzResearch.WordTrace]
  refine ⟨20464122915321213574404355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27285497220428284765872473 20464122915321213574404355)
  ·
    refine ⟨30696184372981820361606533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20464122915321213574404355 30696184372981820361606533)
    ·
      refine ⟨5755534569934091317801225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30696184372981820361606533 5755534569934091317801225)
      ·
        refine ⟨4316650927450568488350919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5755534569934091317801225 4316650927450568488350919)
        ·
          refine ⟨6474976391175852732526379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4316650927450568488350919 6474976391175852732526379)
          ·
            refine ⟨9712464586763779098789569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6474976391175852732526379 9712464586763779098789569)
            ·
              refine ⟨7284348440072834324092177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9712464586763779098789569 7284348440072834324092177)
              ·
                refine ⟨5463261330054625743069133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7284348440072834324092177 5463261330054625743069133)
                ·
                  refine ⟨2048722998770484653650925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5463261330054625743069133 2048722998770484653650925)
                  ·
                    refine ⟨768271124538931745119097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2048722998770484653650925 768271124538931745119097)
                    ·
                      refine ⟨576203343404198808839323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 768271124538931745119097 576203343404198808839323)
                      ·
                        rfl

theorem cell23_1122152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 3, 3, 2].length) (baseStart_1122152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1122152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1122152 prefixEnd_1122152 := by exact prefixLift 1122152
  have htrace : WordTrace (prefixWord ++ tailWord_1122152) baseStart_1122152 baseEnd_1122152 := by
    simpa [prefixWord, tailWord_1122152, baseEnd_1122152] using wordTrace_append hprefix tailTrace_1122152
  have hstable : (prefixWord ++ tailWord_1122152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122152).length < 2 ^ (prefixWord ++ tailWord_1122152).sum := by decide
  have hdescent : baseEnd_1122152 < baseStart_1122152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122199 : List Nat := [1, 1, 3, 3, 1, 3, 1, 4, 2, 2, 2]
def baseStart_1122199 : Nat := 118140960795 + 1122199 * 2 ^ 59
def prefixEnd_1122199 : Nat := 4983230072969 + 3 ^ 40 * 1122199 * 2
def baseEnd_1122199 : Nat := 576227476994960124951607

theorem tailTrace_1122199 : CollatzResearch.WordTrace tailWord_1122199 prefixEnd_1122199 576227476994960124951607 := by
  unfold tailWord_1122199
  simp only [CollatzResearch.WordTrace]
  refine ⟨40929960061472154175769651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27286640040981436117179767 40929960061472154175769651)
  ·
    refine ⟨61394940092208231263654477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40929960061472154175769651 61394940092208231263654477)
    ·
      refine ⟨23023102534578086723870429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61394940092208231263654477 23023102534578086723870429)
      ·
        refine ⟨8633663450466782521451411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23023102534578086723870429 8633663450466782521451411)
        ·
          refine ⟨12950495175700173782177117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8633663450466782521451411 12950495175700173782177117)
          ·
            refine ⟨4856435690887565168316419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12950495175700173782177117 4856435690887565168316419)
            ·
              refine ⟨7284653536331347752474629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4856435690887565168316419 7284653536331347752474629)
              ·
                refine ⟨1365872538062127703588993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7284653536331347752474629 1365872538062127703588993)
                ·
                  refine ⟨1024404403546595777691745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1365872538062127703588993 1024404403546595777691745)
                  ·
                    refine ⟨768303302659946833268809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1024404403546595777691745 768303302659946833268809)
                    ·
                      refine ⟨576227476994960124951607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 768303302659946833268809 576227476994960124951607)
                      ·
                        rfl

theorem cell23_1122199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 4, 2, 2, 2].length) (baseStart_1122199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1122199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1122199 prefixEnd_1122199 := by exact prefixLift 1122199
  have htrace : WordTrace (prefixWord ++ tailWord_1122199) baseStart_1122199 baseEnd_1122199 := by
    simpa [prefixWord, tailWord_1122199, baseEnd_1122199] using wordTrace_append hprefix tailTrace_1122199
  have hstable : (prefixWord ++ tailWord_1122199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122199).length < 2 ^ (prefixWord ++ tailWord_1122199).sum := by decide
  have hdescent : baseEnd_1122199 < baseStart_1122199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122208 : List Nat := [2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 8]
def baseStart_1122208 : Nat := 118140960795 + 1122208 * 2 ^ 59
def prefixEnd_1122208 : Nat := 4983230072969 + 3 ^ 40 * 1122208 * 2
def baseEnd_1122208 : Nat := 576232098320850589739065

theorem tailTrace_1122208 : CollatzResearch.WordTrace tailWord_1122208 prefixEnd_1122208 576232098320850589739065 := by
  unfold tailWord_1122208
  simp only [CollatzResearch.WordTrace]
  refine ⟨20465144159219774356423639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27286858878959699141898185 20465144159219774356423639)
  ·
    refine ⟨30697716238829661534635459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20465144159219774356423639 30697716238829661534635459)
    ·
      refine ⟨46046574358244492301953189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30697716238829661534635459 46046574358244492301953189)
      ·
        refine ⟨8633732692170842306616223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46046574358244492301953189 8633732692170842306616223)
        ·
          refine ⟨12950599038256263459924335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8633732692170842306616223 12950599038256263459924335)
          ·
            refine ⟨19425898557384395189886503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12950599038256263459924335 19425898557384395189886503)
            ·
              refine ⟨29138847836076592784829755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19425898557384395189886503 29138847836076592784829755)
              ·
                refine ⟨43708271754114889177244633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29138847836076592784829755 43708271754114889177244633)
                ·
                  refine ⟨32781203815586166882933475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43708271754114889177244633 32781203815586166882933475)
                  ·
                    refine ⟨49171805723379250324400213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32781203815586166882933475 49171805723379250324400213)
                    ·
                      refine ⟨576232098320850589739065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 49171805723379250324400213 576232098320850589739065)
                      ·
                        rfl

theorem cell23_1122208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_1122208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1122208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1122208 prefixEnd_1122208 := by exact prefixLift 1122208
  have htrace : WordTrace (prefixWord ++ tailWord_1122208) baseStart_1122208 baseEnd_1122208 := by
    simpa [prefixWord, tailWord_1122208, baseEnd_1122208] using wordTrace_append hprefix tailTrace_1122208
  have hstable : (prefixWord ++ tailWord_1122208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122208).length < 2 ^ (prefixWord ++ tailWord_1122208).sum := by decide
  have hdescent : baseEnd_1122208 < baseStart_1122208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122255 : List Nat := [1, 1, 2, 1, 1, 5, 2, 1, 4, 1, 4]
def baseStart_1122255 : Nat := 118140960795 + 1122255 * 2 ^ 59
def prefixEnd_1122255 : Nat := 4983230072969 + 3 ^ 40 * 1122255 * 2
def baseEnd_1122255 : Nat := 576256231911611905851349

theorem tailTrace_1122255 : CollatzResearch.WordTrace tailWord_1122255 prefixEnd_1122255 576256231911611905851349 := by
  unfold tailWord_1122255
  simp only [CollatzResearch.WordTrace]
  refine ⟨40932002549269275739808219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27288001699512850493205479 40932002549269275739808219)
  ·
    refine ⟨61398003823903913609712329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40932002549269275739808219 61398003823903913609712329)
    ·
      refine ⟨46048502867927935207284247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61398003823903913609712329 46048502867927935207284247)
      ·
        refine ⟨69072754301891902810926371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46048502867927935207284247 69072754301891902810926371)
        ·
          refine ⟨103609131452837854216389557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69072754301891902810926371 103609131452837854216389557)
          ·
            refine ⟨9713356073703548832786521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 103609131452837854216389557 9713356073703548832786521)
            ·
              refine ⟨7285017055277661624589891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9713356073703548832786521 7285017055277661624589891)
              ·
                refine ⟨10927525582916492436884837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7285017055277661624589891 10927525582916492436884837)
                ·
                  refine ⟨2048911046796842331915907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10927525582916492436884837 2048911046796842331915907)
                  ·
                    refine ⟨3073366570195263497873861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2048911046796842331915907 3073366570195263497873861)
                    ·
                      refine ⟨576256231911611905851349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3073366570195263497873861 576256231911611905851349)
                      ·
                        rfl

theorem cell23_1122255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 4, 1, 4].length) (baseStart_1122255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1122255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1122255 prefixEnd_1122255 := by exact prefixLift 1122255
  have htrace : WordTrace (prefixWord ++ tailWord_1122255) baseStart_1122255 baseEnd_1122255 := by
    simpa [prefixWord, tailWord_1122255, baseEnd_1122255] using wordTrace_append hprefix tailTrace_1122255
  have hstable : (prefixWord ++ tailWord_1122255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122255).length < 2 ^ (prefixWord ++ tailWord_1122255).sum := by decide
  have hdescent : baseEnd_1122255 < baseStart_1122255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122282 : List Nat := [3, 1, 3, 1, 2, 1, 1, 4, 3, 4]
def baseStart_1122282 : Nat := 118140960795 + 1122282 * 2 ^ 59
def prefixEnd_1122282 : Nat := 4983230072969 + 3 ^ 40 * 1122282 * 2
def baseEnd_1122282 : Nat := 192090031963094433404575

theorem tailTrace_1122282 : CollatzResearch.WordTrace tailWord_1122282 prefixEnd_1122282 192090031963094433404575 := by
  unfold tailWord_1122282
  simp only [CollatzResearch.WordTrace]
  refine ⟨10233246830042864837760275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27288658213447639567360733 10233246830042864837760275)
  ·
    refine ⟨15349870245064297256640413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10233246830042864837760275 15349870245064297256640413)
    ·
      refine ⟨5756201341899111471240155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15349870245064297256640413 5756201341899111471240155)
      ·
        refine ⟨8634302012848667206860233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5756201341899111471240155 8634302012848667206860233)
        ·
          refine ⟨6475726509636500405145175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8634302012848667206860233 6475726509636500405145175)
          ·
            refine ⟨9713589764454750607717763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6475726509636500405145175 9713589764454750607717763)
            ·
              refine ⟨14570384646682125911576645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9713589764454750607717763 14570384646682125911576645)
              ·
                refine ⟨2731947121252898608420621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14570384646682125911576645 2731947121252898608420621)
                ·
                  refine ⟨1024480170469836978157733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2731947121252898608420621 1024480170469836978157733)
                  ·
                    refine ⟨192090031963094433404575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1024480170469836978157733 192090031963094433404575)
                    ·
                      rfl

theorem cell23_1122282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 4, 3, 4].length) (baseStart_1122282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1122282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1122282 prefixEnd_1122282 := by exact prefixLift 1122282
  have htrace : WordTrace (prefixWord ++ tailWord_1122282) baseStart_1122282 baseEnd_1122282 := by
    simpa [prefixWord, tailWord_1122282, baseEnd_1122282] using wordTrace_append hprefix tailTrace_1122282
  have hstable : (prefixWord ++ tailWord_1122282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122282).length < 2 ^ (prefixWord ++ tailWord_1122282).sum := by decide
  have hdescent : baseEnd_1122282 < baseStart_1122282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122299 : List Nat := [1, 1, 1, 1, 1, 3, 7, 3, 1, 4]
def baseStart_1122299 : Nat := 118140960795 + 1122299 * 2 ^ 59
def prefixEnd_1122299 : Nat := 4983230072969 + 3 ^ 40 * 1122299 * 2
def baseEnd_1122299 : Nat := 192092941686803244567049

theorem tailTrace_1122299 : CollatzResearch.WordTrace tailWord_1122299 prefixEnd_1122299 192092941686803244567049 := by
  unfold tailWord_1122299
  simp only [CollatzResearch.WordTrace]
  refine ⟨40933607361109871254409951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27289071574073247502939967 40933607361109871254409951)
  ·
    refine ⟨61400411041664806881614927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40933607361109871254409951 61400411041664806881614927)
    ·
      refine ⟨92100616562497210322422391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61400411041664806881614927 92100616562497210322422391)
      ·
        refine ⟨138150924843745815483633587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92100616562497210322422391 138150924843745815483633587)
        ·
          refine ⟨207226387265618723225450381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138150924843745815483633587 207226387265618723225450381)
          ·
            refine ⟨77709895224607021209543893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 207226387265618723225450381 77709895224607021209543893)
            ·
              refine ⟨1821325669326727059598685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 77709895224607021209543893 1821325669326727059598685)
              ·
                refine ⟨682997125997522647349507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1821325669326727059598685 682997125997522647349507)
                ·
                  refine ⟨1024495688996283971024261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 682997125997522647349507 1024495688996283971024261)
                  ·
                    refine ⟨192092941686803244567049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1024495688996283971024261 192092941686803244567049)
                    ·
                      rfl

theorem cell23_1122299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 3, 1, 4].length) (baseStart_1122299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1122299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1122299 prefixEnd_1122299 := by exact prefixLift 1122299
  have htrace : WordTrace (prefixWord ++ tailWord_1122299) baseStart_1122299 baseEnd_1122299 := by
    simpa [prefixWord, tailWord_1122299, baseEnd_1122299] using wordTrace_append hprefix tailTrace_1122299
  have hstable : (prefixWord ++ tailWord_1122299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122299).length < 2 ^ (prefixWord ++ tailWord_1122299).sum := by decide
  have hdescent : baseEnd_1122299 < baseStart_1122299 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122316 : List Nat := [2, 2, 1, 2, 3, 1, 5, 2, 1, 4]
def baseStart_1122316 : Nat := 118140960795 + 1122316 * 2 ^ 59
def prefixEnd_1122316 : Nat := 4983230072969 + 3 ^ 40 * 1122316 * 2
def baseEnd_1122316 : Nat := 192095851410512055729523

theorem tailTrace_1122316 : CollatzResearch.WordTrace tailWord_1122316 prefixEnd_1122316 192095851410512055729523 := by
  unfold tailWord_1122316
  simp only [CollatzResearch.WordTrace]
  refine ⟨20467113701024141578889401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27289484934698855438519201 20467113701024141578889401)
  ·
    refine ⟨15350335275768106184167051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20467113701024141578889401 15350335275768106184167051)
    ·
      refine ⟨23025502913652159276250577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15350335275768106184167051 23025502913652159276250577)
      ·
        refine ⟨17269127185239119457187933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23025502913652159276250577 17269127185239119457187933)
        ·
          refine ⟨6475922694464669796445475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17269127185239119457187933 6475922694464669796445475)
          ·
            refine ⟨9713884041697004694668213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6475922694464669796445475 9713884041697004694668213)
            ·
              refine ⟨910676628909094190125145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9713884041697004694668213 910676628909094190125145)
              ·
                refine ⟨683007471681820642593859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 910676628909094190125145 683007471681820642593859)
                ·
                  refine ⟨1024511207522730963890789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 683007471681820642593859 1024511207522730963890789)
                  ·
                    refine ⟨192095851410512055729523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1024511207522730963890789 192095851410512055729523)
                    ·
                      rfl

theorem cell23_1122316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 5, 2, 1, 4].length) (baseStart_1122316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1122316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1122316 prefixEnd_1122316 := by exact prefixLift 1122316
  have htrace : WordTrace (prefixWord ++ tailWord_1122316) baseStart_1122316 baseEnd_1122316 := by
    simpa [prefixWord, tailWord_1122316, baseEnd_1122316] using wordTrace_append hprefix tailTrace_1122316
  have hstable : (prefixWord ++ tailWord_1122316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122316).length < 2 ^ (prefixWord ++ tailWord_1122316).sum := by decide
  have hdescent : baseEnd_1122316 < baseStart_1122316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122355 : List Nat := [1, 1, 1, 2, 4, 1, 3, 1, 3, 6]
def baseStart_1122355 : Nat := 118140960795 + 1122355 * 2 ^ 59
def prefixEnd_1122355 : Nat := 4983230072969 + 3 ^ 40 * 1122355 * 2
def baseEnd_1122355 : Nat := 192102526659020504866963

theorem tailTrace_1122355 : CollatzResearch.WordTrace tailWord_1122355 prefixEnd_1122355 192102526659020504866963 := by
  unfold tailWord_1122355
  simp only [CollatzResearch.WordTrace]
  refine ⟨40935649848906992818448519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27290433232604661878965679 40935649848906992818448519)
  ·
    refine ⟨61403474773360489227672779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40935649848906992818448519 61403474773360489227672779)
    ·
      refine ⟨92105212160040733841509169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61403474773360489227672779 92105212160040733841509169)
      ·
        refine ⟨69078909120030550381131877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92105212160040733841509169 69078909120030550381131877)
        ·
          refine ⟨12952295460005728196462227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69078909120030550381131877 12952295460005728196462227)
          ·
            refine ⟨19428443190008592294693341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12952295460005728196462227 19428443190008592294693341)
            ·
              refine ⟨7285666196253222110510003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19428443190008592294693341 7285666196253222110510003)
              ·
                refine ⟨10928499294379833165765005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7285666196253222110510003 10928499294379833165765005)
                ·
                  refine ⟨4098187235392437437161877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10928499294379833165765005 4098187235392437437161877)
                  ·
                    refine ⟨192102526659020504866963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4098187235392437437161877 192102526659020504866963)
                    ·
                      rfl

theorem cell23_1122355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 3, 6].length) (baseStart_1122355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1122355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1122355 prefixEnd_1122355 := by exact prefixLift 1122355
  have htrace : WordTrace (prefixWord ++ tailWord_1122355) baseStart_1122355 baseEnd_1122355 := by
    simpa [prefixWord, tailWord_1122355, baseEnd_1122355] using wordTrace_append hprefix tailTrace_1122355
  have hstable : (prefixWord ++ tailWord_1122355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122355).length < 2 ^ (prefixWord ++ tailWord_1122355).sum := by decide
  have hdescent : baseEnd_1122355 < baseStart_1122355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122389 : List Nat := [1, 3, 2, 2, 1, 3, 2, 3, 2, 4]
def baseStart_1122389 : Nat := 118140960795 + 1122389 * 2 ^ 59
def prefixEnd_1122389 : Nat := 4983230072969 + 3 ^ 40 * 1122389 * 2
def baseEnd_1122389 : Nat := 192108346106438127191911

theorem tailTrace_1122389 : CollatzResearch.WordTrace tailWord_1122389 prefixEnd_1122389 192108346106438127191911 := by
  unfold tailWord_1122389
  simp only [CollatzResearch.WordTrace]
  refine ⟨40936889930783816625186221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27291259953855877750124147 40936889930783816625186221)
  ·
    refine ⟨15351333724043931234444833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40936889930783816625186221 15351333724043931234444833)
    ·
      refine ⟨11513500293032948425833625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15351333724043931234444833 11513500293032948425833625)
      ·
        refine ⟨8635125219774711319375219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11513500293032948425833625 8635125219774711319375219)
        ·
          refine ⟨12952687829662066979062829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8635125219774711319375219 12952687829662066979062829)
          ·
            refine ⟨4857257936123275117148561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12952687829662066979062829 4857257936123275117148561)
            ·
              refine ⟨3642943452092456337861421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4857257936123275117148561 3642943452092456337861421)
              ·
                refine ⟨1366103794534671126698033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3642943452092456337861421 1366103794534671126698033)
                ·
                  refine ⟨1024577845901003345023525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1366103794534671126698033 1024577845901003345023525)
                  ·
                    refine ⟨192108346106438127191911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1024577845901003345023525 192108346106438127191911)
                    ·
                      rfl

theorem cell23_1122389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 3, 2, 4].length) (baseStart_1122389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1122389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1122389 prefixEnd_1122389 := by exact prefixLift 1122389
  have htrace : WordTrace (prefixWord ++ tailWord_1122389) baseStart_1122389 baseEnd_1122389 := by
    simpa [prefixWord, tailWord_1122389, baseEnd_1122389] using wordTrace_append hprefix tailTrace_1122389
  have hstable : (prefixWord ++ tailWord_1122389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122389).length < 2 ^ (prefixWord ++ tailWord_1122389).sum := by decide
  have hdescent : baseEnd_1122389 < baseStart_1122389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122392 : List Nat := [2, 1, 2, 2, 1, 4, 1, 3, 1, 2, 4]
def baseStart_1122392 : Nat := 118140960795 + 1122392 * 2 ^ 59
def prefixEnd_1122392 : Nat := 4983230072969 + 3 ^ 40 * 1122392 * 2
def baseEnd_1122392 : Nat := 576326578761277869838219

theorem tailTrace_1122392 : CollatzResearch.WordTrace tailWord_1122392 prefixEnd_1122392 576326578761277869838219 := by
  unfold tailWord_1122392
  simp only [CollatzResearch.WordTrace]
  refine ⟨20468499674886474068772715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27291332899848632091696953 20468499674886474068772715)
  ·
    refine ⟨30702749512329711103159073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20468499674886474068772715 30702749512329711103159073)
    ·
      refine ⟨23027062134247283327369305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30702749512329711103159073 23027062134247283327369305)
      ·
        refine ⟨17270296600685462495526979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23027062134247283327369305 17270296600685462495526979)
        ·
          refine ⟨25905444901028193743290469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17270296600685462495526979 25905444901028193743290469)
          ·
            refine ⟨4857270918942786326866963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25905444901028193743290469 4857270918942786326866963)
            ·
              refine ⟨7285906378414179490300445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4857270918942786326866963 7285906378414179490300445)
              ·
                refine ⟨2732214891905317308862667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7285906378414179490300445 2732214891905317308862667)
                ·
                  refine ⟨4098322337857975963294001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2732214891905317308862667 4098322337857975963294001)
                  ·
                    refine ⟨3073741753393481972470501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4098322337857975963294001 3073741753393481972470501)
                    ·
                      refine ⟨576326578761277869838219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3073741753393481972470501 576326578761277869838219)
                      ·
                        rfl

theorem cell23_1122392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 3, 1, 2, 4].length) (baseStart_1122392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1122392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1122392 prefixEnd_1122392 := by exact prefixLift 1122392
  have htrace : WordTrace (prefixWord ++ tailWord_1122392) baseStart_1122392 baseEnd_1122392 := by
    simpa [prefixWord, tailWord_1122392, baseEnd_1122392] using wordTrace_append hprefix tailTrace_1122392
  have hstable : (prefixWord ++ tailWord_1122392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122392).length < 2 ^ (prefixWord ++ tailWord_1122392).sum := by decide
  have hdescent : baseEnd_1122392 < baseStart_1122392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122396 : List Nat := [2, 2, 4, 1, 1, 2, 1, 1, 5, 2, 2]
def baseStart_1122396 : Nat := 118140960795 + 1122396 * 2 ^ 59
def prefixEnd_1122396 : Nat := 4983230072969 + 3 ^ 40 * 1122396 * 2
def baseEnd_1122396 : Nat := 576328632683895854188201

theorem tailTrace_1122396 : CollatzResearch.WordTrace tailWord_1122396 prefixEnd_1122396 576328632683895854188201 := by
  unfold tailWord_1122396
  simp only [CollatzResearch.WordTrace]
  refine ⟨20468572620879228410345521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27291430161172304547127361 20468572620879228410345521)
  ·
    refine ⟨15351429465659421307759141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20468572620879228410345521 15351429465659421307759141)
    ·
      refine ⟨2878393024811141495204839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15351429465659421307759141 2878393024811141495204839)
      ·
        refine ⟨4317589537216712242807259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2878393024811141495204839 4317589537216712242807259)
        ·
          refine ⟨6476384305825068364210889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4317589537216712242807259 6476384305825068364210889)
          ·
            refine ⟨4857288229368801273158167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6476384305825068364210889 4857288229368801273158167)
            ·
              refine ⟨7285932344053201909737251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4857288229368801273158167 7285932344053201909737251)
              ·
                refine ⟨10928898516079802864605877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7285932344053201909737251 10928898516079802864605877)
                ·
                  refine ⟨1024584235882481518556801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10928898516079802864605877 1024584235882481518556801)
                  ·
                    refine ⟨768438176911861138917601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1024584235882481518556801 768438176911861138917601)
                    ·
                      refine ⟨576328632683895854188201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 768438176911861138917601 576328632683895854188201)
                      ·
                        rfl

theorem cell23_1122396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 5, 2, 2].length) (baseStart_1122396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1122396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1122396 prefixEnd_1122396 := by exact prefixLift 1122396
  have htrace : WordTrace (prefixWord ++ tailWord_1122396) baseStart_1122396 baseEnd_1122396 := by
    simpa [prefixWord, tailWord_1122396, baseEnd_1122396] using wordTrace_append hprefix tailTrace_1122396
  have hstable : (prefixWord ++ tailWord_1122396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122396).length < 2 ^ (prefixWord ++ tailWord_1122396).sum := by decide
  have hdescent : baseEnd_1122396 < baseStart_1122396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122416 : List Nat := [2, 1, 1, 1, 5, 2, 4, 1, 1, 2, 3]
def baseStart_1122416 : Nat := 118140960795 + 1122416 * 2 ^ 59
def prefixEnd_1122416 : Nat := 4983230072969 + 3 ^ 40 * 1122416 * 2
def baseEnd_1122416 : Nat := 576338902296985775938109

theorem tailTrace_1122416 : CollatzResearch.WordTrace tailWord_1122416 prefixEnd_1122416 576338902296985775938109 := by
  unfold tailWord_1122416
  simp only [CollatzResearch.WordTrace]
  refine ⟨20468937350843000118209551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27291916467790666824279401 20468937350843000118209551)
  ·
    refine ⟨30703406026264500177314327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20468937350843000118209551 30703406026264500177314327)
    ·
      refine ⟨46055109039396750265971491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30703406026264500177314327 46055109039396750265971491)
      ·
        refine ⟨69082663559095125398957237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46055109039396750265971491 69082663559095125398957237)
        ·
          refine ⟨6476499708665168006152241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 69082663559095125398957237 6476499708665168006152241)
          ·
            refine ⟨4857374781498876004614181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6476499708665168006152241 4857374781498876004614181)
            ·
              refine ⟨910757771531039250865159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4857374781498876004614181 910757771531039250865159)
              ·
                refine ⟨1366136657296558876297739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 910757771531039250865159 1366136657296558876297739)
                ·
                  refine ⟨2049204985944838314446609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1366136657296558876297739 2049204985944838314446609)
                  ·
                    refine ⟨1536903739458628735834957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2049204985944838314446609 1536903739458628735834957)
                    ·
                      refine ⟨576338902296985775938109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1536903739458628735834957 576338902296985775938109)
                      ·
                        rfl

theorem cell23_1122416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 4, 1, 1, 2, 3].length) (baseStart_1122416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1122416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1122416 prefixEnd_1122416 := by exact prefixLift 1122416
  have htrace : WordTrace (prefixWord ++ tailWord_1122416) baseStart_1122416 baseEnd_1122416 := by
    simpa [prefixWord, tailWord_1122416, baseEnd_1122416] using wordTrace_append hprefix tailTrace_1122416
  have hstable : (prefixWord ++ tailWord_1122416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122416).length < 2 ^ (prefixWord ++ tailWord_1122416).sum := by decide
  have hdescent : baseEnd_1122416 < baseStart_1122416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122439 : List Nat := [1, 1, 4, 2, 1, 1, 2, 1, 5, 3, 2]
def baseStart_1122439 : Nat := 118140960795 + 1122439 * 2 ^ 59
def prefixEnd_1122439 : Nat := 4983230072969 + 3 ^ 40 * 1122439 * 2
def baseEnd_1122439 : Nat := 576350712352039185950503

theorem tailTrace_1122439 : CollatzResearch.WordTrace tailWord_1122439 prefixEnd_1122439 576350712352039185950503 := by
  unfold tailWord_1122439
  simp only [CollatzResearch.WordTrace]
  refine ⟨40938713580602675164506371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27292475720401783443004247 40938713580602675164506371)
  ·
    refine ⟨61408070370904012746759557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40938713580602675164506371 61408070370904012746759557)
    ·
      refine ⟨11514013194544502390017417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61408070370904012746759557 11514013194544502390017417)
      ·
        refine ⟨8635509895908376792513063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11514013194544502390017417 8635509895908376792513063)
        ·
          refine ⟨12953264843862565188769595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8635509895908376792513063 12953264843862565188769595)
          ·
            refine ⟨19429897265793847783154393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12953264843862565188769595 19429897265793847783154393)
            ·
              refine ⟨14572422949345385837365795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19429897265793847783154393 14572422949345385837365795)
              ·
                refine ⟨21858634424018078756048693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14572422949345385837365795 21858634424018078756048693)
                ·
                  refine ⟨2049246977251694883379565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21858634424018078756048693 2049246977251694883379565)
                  ·
                    refine ⟨768467616469385581267337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2049246977251694883379565 768467616469385581267337)
                    ·
                      refine ⟨576350712352039185950503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 768467616469385581267337 576350712352039185950503)
                      ·
                        rfl

theorem cell23_1122439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 5, 3, 2].length) (baseStart_1122439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1122439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1122439 prefixEnd_1122439 := by exact prefixLift 1122439
  have htrace : WordTrace (prefixWord ++ tailWord_1122439) baseStart_1122439 baseEnd_1122439 := by
    simpa [prefixWord, tailWord_1122439, baseEnd_1122439] using wordTrace_append hprefix tailTrace_1122439
  have hstable : (prefixWord ++ tailWord_1122439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122439).length < 2 ^ (prefixWord ++ tailWord_1122439).sum := by decide
  have hdescent : baseEnd_1122439 < baseStart_1122439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122469 : List Nat := [1, 3, 1, 2, 1, 3, 2, 1, 3, 4, 2]
def baseStart_1122469 : Nat := 118140960795 + 1122469 * 2 ^ 59
def prefixEnd_1122469 : Nat := 4983230072969 + 3 ^ 40 * 1122469 * 2
def baseEnd_1122469 : Nat := 576366116771674068575365

theorem tailTrace_1122469 : CollatzResearch.WordTrace tailWord_1122469 prefixEnd_1122469 576366116771674068575365 := by
  unfold tailWord_1122469
  simp only [CollatzResearch.WordTrace]
  refine ⟨40939807770493990288098461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27293205180329326858732307 40939807770493990288098461)
  ·
    refine ⟨15352427913935246358036923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40939807770493990288098461 15352427913935246358036923)
    ·
      refine ⟨23028641870902869537055385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15352427913935246358036923 23028641870902869537055385)
      ·
        refine ⟨17271481403177152152791539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23028641870902869537055385 17271481403177152152791539)
        ·
          refine ⟨25907222104765728229187309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17271481403177152152791539 25907222104765728229187309)
          ·
            refine ⟨9715208289287148085945241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25907222104765728229187309 9715208289287148085945241)
            ·
              refine ⟨7286406216965361064458931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9715208289287148085945241 7286406216965361064458931)
              ·
                refine ⟨10929609325448041596688397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7286406216965361064458931 10929609325448041596688397)
                ·
                  refine ⟨4098603497043015598758149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10929609325448041596688397 4098603497043015598758149)
                  ·
                    refine ⟨768488155695565424767153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4098603497043015598758149 768488155695565424767153)
                    ·
                      refine ⟨576366116771674068575365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 768488155695565424767153 576366116771674068575365)
                      ·
                        rfl

theorem cell23_1122469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 3, 4, 2].length) (baseStart_1122469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1122469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1122469 prefixEnd_1122469 := by exact prefixLift 1122469
  have htrace : WordTrace (prefixWord ++ tailWord_1122469) baseStart_1122469 baseEnd_1122469 := by
    simpa [prefixWord, tailWord_1122469, baseEnd_1122469] using wordTrace_append hprefix tailTrace_1122469
  have hstable : (prefixWord ++ tailWord_1122469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122469).length < 2 ^ (prefixWord ++ tailWord_1122469).sum := by decide
  have hdescent : baseEnd_1122469 < baseStart_1122469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122497 : List Nat := [1, 2, 6, 1, 2, 2, 2, 1, 2, 1, 3]
def baseStart_1122497 : Nat := 118140960795 + 1122497 * 2 ^ 59
def prefixEnd_1122497 : Nat := 4983230072969 + 3 ^ 40 * 1122497 * 2
def baseEnd_1122497 : Nat := 576380494229999959025237

theorem tailTrace_1122497 : CollatzResearch.WordTrace tailWord_1122497 prefixEnd_1122497 576380494229999959025237 := by
  unfold tailWord_1122497
  simp only [CollatzResearch.WordTrace]
  refine ⟨40940829014392551070117745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27293886009595034046745163 40940829014392551070117745)
  ·
    refine ⟨30705621760794413302588309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40940829014392551070117745 30705621760794413302588309)
    ·
      refine ⟨1439326020037238123558827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 30705621760794413302588309 1439326020037238123558827)
      ·
        refine ⟨2158989030055857185338241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1439326020037238123558827 2158989030055857185338241)
        ·
          refine ⟨1619241772541892889003681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2158989030055857185338241 1619241772541892889003681)
          ·
            refine ⟨1214431329406419666752761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1619241772541892889003681 1214431329406419666752761)
            ·
              refine ⟨910823497054814750064571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1214431329406419666752761 910823497054814750064571)
              ·
                refine ⟨1366235245582222125096857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 910823497054814750064571 1366235245582222125096857)
                ·
                  refine ⟨1024676434186666593822643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1366235245582222125096857 1024676434186666593822643)
                  ·
                    refine ⟨1537014651279999890733965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1024676434186666593822643 1537014651279999890733965)
                    ·
                      refine ⟨576380494229999959025237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1537014651279999890733965 576380494229999959025237)
                      ·
                        rfl

theorem cell23_1122497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_1122497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1122497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1122497 prefixEnd_1122497 := by exact prefixLift 1122497
  have htrace : WordTrace (prefixWord ++ tailWord_1122497) baseStart_1122497 baseEnd_1122497 := by
    simpa [prefixWord, tailWord_1122497, baseEnd_1122497] using wordTrace_append hprefix tailTrace_1122497
  have hstable : (prefixWord ++ tailWord_1122497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122497).length < 2 ^ (prefixWord ++ tailWord_1122497).sum := by decide
  have hdescent : baseEnd_1122497 < baseStart_1122497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122522 : List Nat := [3, 1, 1, 2, 2, 1, 2, 3, 1, 7]
def baseStart_1122522 : Nat := 118140960795 + 1122522 * 2 ^ 59
def prefixEnd_1122522 : Nat := 4983230072969 + 3 ^ 40 * 1122522 * 2
def baseEnd_1122522 : Nat := 192131110415454120404207

theorem tailTrace_1122522 : CollatzResearch.WordTrace tailWord_1122522 prefixEnd_1122522 192131110415454120404207 := by
  unfold tailWord_1122522
  simp only [CollatzResearch.WordTrace]
  refine ⟨10235435209825495084944455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27294493892867986893185213 10235435209825495084944455)
  ·
    refine ⟨15353152814738242627416683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10235435209825495084944455 15353152814738242627416683)
    ·
      refine ⟨23029729222107363941125025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15353152814738242627416683 23029729222107363941125025)
      ·
        refine ⟨17272296916580522955843769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23029729222107363941125025 17272296916580522955843769)
        ·
          refine ⟨12954222687435392216882827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17272296916580522955843769 12954222687435392216882827)
          ·
            refine ⟨19431334031153088325324241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12954222687435392216882827 19431334031153088325324241)
            ·
              refine ⟨14573500523364816243993181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19431334031153088325324241 14573500523364816243993181)
              ·
                refine ⟨5465062696261806091497443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14573500523364816243993181 5465062696261806091497443)
                ·
                  refine ⟨8197594044392709137246165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5465062696261806091497443 8197594044392709137246165)
                  ·
                    refine ⟨192131110415454120404207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8197594044392709137246165 192131110415454120404207)
                    ·
                      rfl

theorem cell23_1122522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 1, 7].length) (baseStart_1122522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1122522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1122522 prefixEnd_1122522 := by exact prefixLift 1122522
  have htrace : WordTrace (prefixWord ++ tailWord_1122522) baseStart_1122522 baseEnd_1122522 := by
    simpa [prefixWord, tailWord_1122522, baseEnd_1122522] using wordTrace_append hprefix tailTrace_1122522
  have hstable : (prefixWord ++ tailWord_1122522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122522).length < 2 ^ (prefixWord ++ tailWord_1122522).sum := by decide
  have hdescent : baseEnd_1122522 < baseStart_1122522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122543 : List Nat := [1, 1, 2, 1, 6, 3, 2, 2, 5]
def baseStart_1122543 : Nat := 118140960795 + 1122543 * 2 ^ 59
def prefixEnd_1122543 : Nat := 4983230072969 + 3 ^ 40 * 1122543 * 2
def baseEnd_1122543 : Nat := 64044901593345197672225

theorem tailTrace_1122543 : CollatzResearch.WordTrace tailWord_1122543 prefixEnd_1122543 64044901593345197672225 := by
  unfold tailWord_1122543
  simp only [CollatzResearch.WordTrace]
  refine ⟨40942506772225900926292283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27295004514817267284194855 40942506772225900926292283)
  ·
    refine ⟨61413760158338851389438425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40942506772225900926292283 61413760158338851389438425)
    ·
      refine ⟨46060320118754138542078819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61413760158338851389438425 46060320118754138542078819)
      ·
        refine ⟨69090480178131207813118229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46060320118754138542078819 69090480178131207813118229)
        ·
          refine ⟨3238616258349900366239917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 69090480178131207813118229 3238616258349900366239917)
          ·
            refine ⟨1214481096881212637339969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3238616258349900366239917 1214481096881212637339969)
            ·
              refine ⟨910860822660909478004977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1214481096881212637339969 910860822660909478004977)
              ·
                refine ⟨683145616995682108503733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 910860822660909478004977 683145616995682108503733)
                ·
                  refine ⟨64044901593345197672225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 683145616995682108503733 64044901593345197672225)
                  ·
                    rfl

theorem cell23_1122543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 2, 2, 5].length) (baseStart_1122543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1122543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1122543 prefixEnd_1122543 := by exact prefixLift 1122543
  have htrace : WordTrace (prefixWord ++ tailWord_1122543) baseStart_1122543 baseEnd_1122543 := by
    simpa [prefixWord, tailWord_1122543, baseEnd_1122543] using wordTrace_append hprefix tailTrace_1122543
  have hstable : (prefixWord ++ tailWord_1122543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122543).length < 2 ^ (prefixWord ++ tailWord_1122543).sum := by decide
  have hdescent : baseEnd_1122543 < baseStart_1122543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122546 : List Nat := [3, 2, 1, 3, 2, 1, 1, 1, 2, 5, 2]
def baseStart_1122546 : Nat := 118140960795 + 1122546 * 2 ^ 59
def prefixEnd_1122546 : Nat := 4983230072969 + 3 ^ 40 * 1122546 * 2
def baseEnd_1122546 : Nat := 576405654782070267312511

theorem tailTrace_1122546 : CollatzResearch.WordTrace tailWord_1122546 prefixEnd_1122546 576405654782070267312511 := by
  unfold tailWord_1122546
  simp only [CollatzResearch.WordTrace]
  refine ⟨10235654047803758109662873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27295077460810021625767661 10235654047803758109662873)
  ·
    refine ⟨7676740535852818582247155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10235654047803758109662873 7676740535852818582247155)
    ·
      refine ⟨11515110803779227873370733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7676740535852818582247155 11515110803779227873370733)
      ·
        refine ⟨4318166551417210452514025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11515110803779227873370733 4318166551417210452514025)
        ·
          refine ⟨3238624913562907839385519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4318166551417210452514025 3238624913562907839385519)
          ·
            refine ⟨4857937370344361759078279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3238624913562907839385519 4857937370344361759078279)
            ·
              refine ⟨7286906055516542638617419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4857937370344361759078279 7286906055516542638617419)
              ·
                refine ⟨10930359083274813957926129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7286906055516542638617419 10930359083274813957926129)
                ·
                  refine ⟨8197769312456110468444597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10930359083274813957926129 8197769312456110468444597)
                  ·
                    refine ⟨768540873042760356416681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8197769312456110468444597 768540873042760356416681)
                    ·
                      refine ⟨576405654782070267312511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 768540873042760356416681 576405654782070267312511)
                      ·
                        rfl

theorem cell23_1122546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 2, 5, 2].length) (baseStart_1122546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1122546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1122546 prefixEnd_1122546 := by exact prefixLift 1122546
  have htrace : WordTrace (prefixWord ++ tailWord_1122546) baseStart_1122546 baseEnd_1122546 := by
    simpa [prefixWord, tailWord_1122546, baseEnd_1122546] using wordTrace_append hprefix tailTrace_1122546
  have hstable : (prefixWord ++ tailWord_1122546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122546).length < 2 ^ (prefixWord ++ tailWord_1122546).sum := by decide
  have hdescent : baseEnd_1122546 < baseStart_1122546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122569 : List Nat := [1, 2, 1, 1, 3, 4, 1, 1, 5, 4]
def baseStart_1122569 : Nat := 118140960795 + 1122569 * 2 ^ 59
def prefixEnd_1122569 : Nat := 4983230072969 + 3 ^ 40 * 1122569 * 2
def baseEnd_1122569 : Nat := 192139154945707892441635

theorem tailTrace_1122569 : CollatzResearch.WordTrace tailWord_1122569 prefixEnd_1122569 192139154945707892441635 := by
  unfold tailWord_1122569
  simp only [CollatzResearch.WordTrace]
  refine ⟨40943455070131707366738761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27295636713421138244492507 40943455070131707366738761)
  ·
    refine ⟨30707591302598780525054071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40943455070131707366738761 30707591302598780525054071)
    ·
      refine ⟨46061386953898170787581107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30707591302598780525054071 46061386953898170787581107)
      ·
        refine ⟨69092080430847256181371661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46061386953898170787581107 69092080430847256181371661)
        ·
          refine ⟨25909530161567721068014373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69092080430847256181371661 25909530161567721068014373)
          ·
            refine ⟨4858036905293947700252695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25909530161567721068014373 4858036905293947700252695)
            ·
              refine ⟨7287055357940921550379043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4858036905293947700252695 7287055357940921550379043)
              ·
                refine ⟨10930583036911382325568565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7287055357940921550379043 10930583036911382325568565)
                ·
                  refine ⟨1024742159710442093022053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10930583036911382325568565 1024742159710442093022053)
                  ·
                    refine ⟨192139154945707892441635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1024742159710442093022053 192139154945707892441635)
                    ·
                      rfl

theorem cell23_1122569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 5, 4].length) (baseStart_1122569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1122569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1122569 prefixEnd_1122569 := by exact prefixLift 1122569
  have htrace : WordTrace (prefixWord ++ tailWord_1122569) baseStart_1122569 baseEnd_1122569 := by
    simpa [prefixWord, tailWord_1122569, baseEnd_1122569] using wordTrace_append hprefix tailTrace_1122569
  have hstable : (prefixWord ++ tailWord_1122569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122569).length < 2 ^ (prefixWord ++ tailWord_1122569).sum := by decide
  have hdescent : baseEnd_1122569 < baseStart_1122569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122636 : List Nat := [2, 2, 1, 3, 2, 1, 1, 3, 1, 5, 2]
def baseStart_1122636 : Nat := 118140960795 + 1122636 * 2 ^ 59
def prefixEnd_1122636 : Nat := 4983230072969 + 3 ^ 40 * 1122636 * 2
def baseEnd_1122636 : Nat := 576451868040974915187097

theorem tailTrace_1122636 : CollatzResearch.WordTrace tailWord_1122636 prefixEnd_1122636 576451868040974915187097 := by
  unfold tailWord_1122636
  simp only [CollatzResearch.WordTrace]
  refine ⟨20472949380444488904713881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27297265840592651872951841 20472949380444488904713881)
  ·
    refine ⟨15354712035333366678535411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20472949380444488904713881 15354712035333366678535411)
    ·
      refine ⟨23032068053000050017803117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15354712035333366678535411 23032068053000050017803117)
      ·
        refine ⟨8637025519875018756676169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23032068053000050017803117 8637025519875018756676169)
        ·
          refine ⟨6477769139906264067507127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8637025519875018756676169 6477769139906264067507127)
          ·
            refine ⟨9716653709859396101260691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6477769139906264067507127 9716653709859396101260691)
            ·
              refine ⟨14574980564789094151891037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9716653709859396101260691 14574980564789094151891037)
              ·
                refine ⟨5465617711795910306959139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14574980564789094151891037 5465617711795910306959139)
                ·
                  refine ⟨8198426567693865460438709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5465617711795910306959139 8198426567693865460438709)
                  ·
                    refine ⟨768602490721299886916129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8198426567693865460438709 768602490721299886916129)
                    ·
                      refine ⟨576451868040974915187097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 768602490721299886916129 576451868040974915187097)
                      ·
                        rfl

theorem cell23_1122636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 1, 5, 2].length) (baseStart_1122636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1122636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1122636 prefixEnd_1122636 := by exact prefixLift 1122636
  have htrace : WordTrace (prefixWord ++ tailWord_1122636) baseStart_1122636 baseEnd_1122636 := by
    simpa [prefixWord, tailWord_1122636, baseEnd_1122636] using wordTrace_append hprefix tailTrace_1122636
  have hstable : (prefixWord ++ tailWord_1122636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122636).length < 2 ^ (prefixWord ++ tailWord_1122636).sum := by decide
  have hdescent : baseEnd_1122636 < baseStart_1122636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122643 : List Nat := [1, 1, 1, 2, 1, 1, 4, 7, 1, 1, 3]
def baseStart_1122643 : Nat := 118140960795 + 1122643 * 2 ^ 59
def prefixEnd_1122643 : Nat := 4983230072969 + 3 ^ 40 * 1122643 * 2
def baseEnd_1122643 : Nat := 576455462405556387799565

theorem tailTrace_1122643 : CollatzResearch.WordTrace tailWord_1122643 prefixEnd_1122643 576455462405556387799565 := by
  unfold tailWord_1122643
  simp only [CollatzResearch.WordTrace]
  refine ⟨40946154071863618004932583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27297436047909078669955055 40946154071863618004932583)
  ·
    refine ⟨61419231107795427007398875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40946154071863618004932583 61419231107795427007398875)
    ·
      refine ⟨92128846661693140511098313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61419231107795427007398875 92128846661693140511098313)
      ·
        refine ⟨69096634996269855383323735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92128846661693140511098313 69096634996269855383323735)
        ·
          refine ⟨103644952494404783074985603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69096634996269855383323735 103644952494404783074985603)
          ·
            refine ⟨155467428741607174612478405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103644952494404783074985603 155467428741607174612478405)
            ·
              refine ⟨29150142889051345239839701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 155467428741607174612478405 29150142889051345239839701)
              ·
                refine ⟨683206473962140904058743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 29150142889051345239839701 683206473962140904058743)
                ·
                  refine ⟨1024809710943211356088115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 683206473962140904058743 1024809710943211356088115)
                  ·
                    refine ⟨1537214566414817034132173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1024809710943211356088115 1537214566414817034132173)
                    ·
                      refine ⟨576455462405556387799565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1537214566414817034132173 576455462405556387799565)
                      ·
                        rfl

theorem cell23_1122643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 7, 1, 1, 3].length) (baseStart_1122643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1122643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1122643 prefixEnd_1122643 := by exact prefixLift 1122643
  have htrace : WordTrace (prefixWord ++ tailWord_1122643) baseStart_1122643 baseEnd_1122643 := by
    simpa [prefixWord, tailWord_1122643, baseEnd_1122643] using wordTrace_append hprefix tailTrace_1122643
  have hstable : (prefixWord ++ tailWord_1122643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122643).length < 2 ^ (prefixWord ++ tailWord_1122643).sum := by decide
  have hdescent : baseEnd_1122643 < baseStart_1122643 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122649 : List Nat := [1, 2, 1, 2, 2, 2, 1, 2, 5, 1, 4]
def baseStart_1122649 : Nat := 118140960795 + 1122649 * 2 ^ 59
def prefixEnd_1122649 : Nat := 4983230072969 + 3 ^ 40 * 1122649 * 2
def baseEnd_1122649 : Nat := 576458543289483364324537

theorem tailTrace_1122649 : CollatzResearch.WordTrace tailWord_1122649 prefixEnd_1122649 576458543289483364324537 := by
  unfold tailWord_1122649
  simp only [CollatzResearch.WordTrace]
  refine ⟨40946372909841881029651001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27297581939894587353100667 40946372909841881029651001)
  ·
    refine ⟨30709779682381410772238251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40946372909841881029651001 30709779682381410772238251)
    ·
      refine ⟨46064669523572116158357377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30709779682381410772238251 46064669523572116158357377)
      ·
        refine ⟨34548502142679087118768033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46064669523572116158357377 34548502142679087118768033)
        ·
          refine ⟨25911376607009315339076025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34548502142679087118768033 25911376607009315339076025)
          ·
            refine ⟨19433532455256986504307019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25911376607009315339076025 19433532455256986504307019)
            ·
              refine ⟨29150298682885479756460529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19433532455256986504307019 29150298682885479756460529)
              ·
                refine ⟨21862724012164109817345397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29150298682885479756460529 21862724012164109817345397)
                ·
                  refine ⟨2049630376140385295376131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21862724012164109817345397 2049630376140385295376131)
                  ·
                    refine ⟨3074445564210577943064197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2049630376140385295376131 3074445564210577943064197)
                    ·
                      refine ⟨576458543289483364324537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3074445564210577943064197 576458543289483364324537)
                      ·
                        rfl

theorem cell23_1122649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 5, 1, 4].length) (baseStart_1122649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1122649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1122649 prefixEnd_1122649 := by exact prefixLift 1122649
  have htrace : WordTrace (prefixWord ++ tailWord_1122649) baseStart_1122649 baseEnd_1122649 := by
    simpa [prefixWord, tailWord_1122649, baseEnd_1122649] using wordTrace_append hprefix tailTrace_1122649
  have hstable : (prefixWord ++ tailWord_1122649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122649).length < 2 ^ (prefixWord ++ tailWord_1122649).sum := by decide
  have hdescent : baseEnd_1122649 < baseStart_1122649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122683 : List Nat := [1, 1, 1, 1, 1, 9, 1, 2, 1, 1, 4]
def baseStart_1122683 : Nat := 118140960795 + 1122683 * 2 ^ 59
def prefixEnd_1122683 : Nat := 4983230072969 + 3 ^ 40 * 1122683 * 2
def baseEnd_1122683 : Nat := 576476001631736231299381

theorem tailTrace_1122683 : CollatzResearch.WordTrace tailWord_1122683 prefixEnd_1122683 576476001631736231299381 := by
  unfold tailWord_1122683
  simp only [CollatzResearch.WordTrace]
  refine ⟨40947612991718704836388703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27298408661145803224259135 40947612991718704836388703)
  ·
    refine ⟨61421419487578057254583055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40947612991718704836388703 61421419487578057254583055)
    ·
      refine ⟨92132129231367085881874583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61421419487578057254583055 92132129231367085881874583)
      ·
        refine ⟨138198193847050628822811875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92132129231367085881874583 138198193847050628822811875)
        ·
          refine ⟨207297290770575943234217813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138198193847050628822811875 207297290770575943234217813)
          ·
            refine ⟨1214632563108843417387995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 207297290770575943234217813 1214632563108843417387995)
            ·
              refine ⟨1821948844663265126081993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1214632563108843417387995 1821948844663265126081993)
              ·
                refine ⟨1366461633497448844561495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1821948844663265126081993 1366461633497448844561495)
                ·
                  refine ⟨2049692450246173266842243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1366461633497448844561495 2049692450246173266842243)
                  ·
                    refine ⟨3074538675369259900263365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2049692450246173266842243 3074538675369259900263365)
                    ·
                      refine ⟨576476001631736231299381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3074538675369259900263365 576476001631736231299381)
                      ·
                        rfl

theorem cell23_1122683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 2, 1, 1, 4].length) (baseStart_1122683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1122683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1122683 prefixEnd_1122683 := by exact prefixLift 1122683
  have htrace : WordTrace (prefixWord ++ tailWord_1122683) baseStart_1122683 baseEnd_1122683 := by
    simpa [prefixWord, tailWord_1122683, baseEnd_1122683] using wordTrace_append hprefix tailTrace_1122683
  have hstable : (prefixWord ++ tailWord_1122683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122683).length < 2 ^ (prefixWord ++ tailWord_1122683).sum := by decide
  have hdescent : baseEnd_1122683 < baseStart_1122683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122696 : List Nat := [2, 1, 3, 3, 1, 1, 3, 2, 1, 2, 4]
def baseStart_1122696 : Nat := 118140960795 + 1122696 * 2 ^ 59
def prefixEnd_1122696 : Nat := 4983230072969 + 3 ^ 40 * 1122696 * 2
def baseEnd_1122696 : Nat := 576482676880244680436821

theorem tailTrace_1122696 : CollatzResearch.WordTrace tailWord_1122696 prefixEnd_1122696 576482676880244680436821 := by
  unfold tailWord_1122696
  simp only [CollatzResearch.WordTrace]
  refine ⟨20474043570335804028305971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27298724760447738704407961 20474043570335804028305971)
  ·
    refine ⟨30711065355503706042458957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20474043570335804028305971 30711065355503706042458957)
    ·
      refine ⟨11516649508313889765922109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30711065355503706042458957 11516649508313889765922109)
      ·
        refine ⟨4318743565617708662220791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11516649508313889765922109 4318743565617708662220791)
        ·
          refine ⟨6478115348426562993331187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4318743565617708662220791 6478115348426562993331187)
          ·
            refine ⟨9717173022639844489996781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6478115348426562993331187 9717173022639844489996781)
            ·
              refine ⟨3643939883489941683748793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9717173022639844489996781 3643939883489941683748793)
              ·
                refine ⟨2732954912617456262811595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3643939883489941683748793 2732954912617456262811595)
                ·
                  refine ⟨4099432368926184394217393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2732954912617456262811595 4099432368926184394217393)
                  ·
                    refine ⟨3074574276694638295663045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4099432368926184394217393 3074574276694638295663045)
                    ·
                      refine ⟨576482676880244680436821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3074574276694638295663045 576482676880244680436821)
                      ·
                        rfl

theorem cell23_1122696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_1122696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1122696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1122696 prefixEnd_1122696 := by exact prefixLift 1122696
  have htrace : WordTrace (prefixWord ++ tailWord_1122696) baseStart_1122696 baseEnd_1122696 := by
    simpa [prefixWord, tailWord_1122696, baseEnd_1122696] using wordTrace_append hprefix tailTrace_1122696
  have hstable : (prefixWord ++ tailWord_1122696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122696).length < 2 ^ (prefixWord ++ tailWord_1122696).sum := by decide
  have hdescent : baseEnd_1122696 < baseStart_1122696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122719 : List Nat := [1, 1, 2, 5, 1, 1, 1, 1, 1, 9]
def baseStart_1122719 : Nat := 118140960795 + 1122719 * 2 ^ 59
def prefixEnd_1122719 : Nat := 4983230072969 + 3 ^ 40 * 1122719 * 2
def baseEnd_1122719 : Nat := 192164828978432696816405

theorem tailTrace_1122719 : CollatzResearch.WordTrace tailWord_1122719 prefixEnd_1122719 192164828978432696816405 := by
  unfold tailWord_1122719
  simp only [CollatzResearch.WordTrace]
  refine ⟨40948926019588282984699211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27299284013058855323132807 40948926019588282984699211)
  ·
    refine ⟨61423389029382424477048817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40948926019588282984699211 61423389029382424477048817)
    ·
      refine ⟨46067541772036818357786613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61423389029382424477048817 46067541772036818357786613)
      ·
        refine ⟨4318832041128451721042495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46067541772036818357786613 4318832041128451721042495)
        ·
          refine ⟨6478248061692677581563743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4318832041128451721042495 6478248061692677581563743)
          ·
            refine ⟨9717372092539016372345615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6478248061692677581563743 9717372092539016372345615)
            ·
              refine ⟨14576058138808524558518423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9717372092539016372345615 14576058138808524558518423)
              ·
                refine ⟨21864087208212786837777635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14576058138808524558518423 21864087208212786837777635)
                ·
                  refine ⟨32796130812319180256666453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21864087208212786837777635 32796130812319180256666453)
                  ·
                    refine ⟨192164828978432696816405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 32796130812319180256666453 192164828978432696816405)
                    ·
                      rfl

theorem cell23_1122719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 9].length) (baseStart_1122719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1122719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1122719 prefixEnd_1122719 := by exact prefixLift 1122719
  have htrace : WordTrace (prefixWord ++ tailWord_1122719) baseStart_1122719 baseEnd_1122719 := by
    simpa [prefixWord, tailWord_1122719, baseEnd_1122719] using wordTrace_append hprefix tailTrace_1122719
  have hstable : (prefixWord ++ tailWord_1122719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122719).length < 2 ^ (prefixWord ++ tailWord_1122719).sum := by decide
  have hdescent : baseEnd_1122719 < baseStart_1122719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122743 : List Nat := [1, 1, 3, 1, 3, 3, 2, 1, 3, 3, 2]
def baseStart_1122743 : Nat := 118140960795 + 1122743 * 2 ^ 59
def prefixEnd_1122743 : Nat := 4983230072969 + 3 ^ 40 * 1122743 * 2
def baseEnd_1122743 : Nat := 576506810471005996549105

theorem tailTrace_1122743 : CollatzResearch.WordTrace tailWord_1122743 prefixEnd_1122743 576506810471005996549105 := by
  unfold tailWord_1122743
  simp only [CollatzResearch.WordTrace]
  refine ⟨40949801371501335083572883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27299867581000890055715255 40949801371501335083572883)
  ·
    refine ⟨61424702057252002625359325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40949801371501335083572883 61424702057252002625359325)
    ·
      refine ⟨23034263271469500984509747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61424702057252002625359325 23034263271469500984509747)
      ·
        refine ⟨34551394907204251476764621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23034263271469500984509747 34551394907204251476764621)
        ·
          refine ⟨12956773090201594303786733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34551394907204251476764621 12956773090201594303786733)
          ·
            refine ⟨4858789908825597863920025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12956773090201594303786733 4858789908825597863920025)
            ·
              refine ⟨3644092431619198397940019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4858789908825597863920025 3644092431619198397940019)
              ·
                refine ⟨5466138647428797596910029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3644092431619198397940019 5466138647428797596910029)
                ·
                  refine ⟨2049801992785799098841261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5466138647428797596910029 2049801992785799098841261)
                  ·
                    refine ⟨768675747294674662065473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2049801992785799098841261 768675747294674662065473)
                    ·
                      refine ⟨576506810471005996549105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 768675747294674662065473 576506810471005996549105)
                      ·
                        rfl

theorem cell23_1122743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 3, 3, 2].length) (baseStart_1122743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1122743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1122743 prefixEnd_1122743 := by exact prefixLift 1122743
  have htrace : WordTrace (prefixWord ++ tailWord_1122743) baseStart_1122743 baseEnd_1122743 := by
    simpa [prefixWord, tailWord_1122743, baseEnd_1122743] using wordTrace_append hprefix tailTrace_1122743
  have hstable : (prefixWord ++ tailWord_1122743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122743).length < 2 ^ (prefixWord ++ tailWord_1122743).sum := by decide
  have hdescent : baseEnd_1122743 < baseStart_1122743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122760 : List Nat := [2, 1, 3, 1, 3, 3, 1, 3, 1, 3, 2]
def baseStart_1122760 : Nat := 118140960795 + 1122760 * 2 ^ 59
def prefixEnd_1122760 : Nat := 4983230072969 + 3 ^ 40 * 1122760 * 2
def baseEnd_1122760 : Nat := 576515539642132430036527

theorem tailTrace_1122760 : CollatzResearch.WordTrace tailWord_1122760 prefixEnd_1122760 576515539642132430036527 := by
  unfold tailWord_1122760
  simp only [CollatzResearch.WordTrace]
  refine ⟨20475210706219873493470867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27300280941626497991294489 20475210706219873493470867)
  ·
    refine ⟨30712816059329810240206301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20475210706219873493470867 30712816059329810240206301)
    ·
      refine ⟨11517306022248678840077363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30712816059329810240206301 11517306022248678840077363)
      ·
        refine ⟨17275959033373018260116045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11517306022248678840077363 17275959033373018260116045)
        ·
          refine ⟨6478484637514881847543517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17275959033373018260116045 6478484637514881847543517)
          ·
            refine ⟨2429431739068080692828819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6478484637514881847543517 2429431739068080692828819)
            ·
              refine ⟨3644147608602121039243229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2429431739068080692828819 3644147608602121039243229)
              ·
                refine ⟨1366555353225795389716211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3644147608602121039243229 1366555353225795389716211)
                ·
                  refine ⟨2049833029838693084574317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1366555353225795389716211 2049833029838693084574317)
                  ·
                    refine ⟨768687386189509906715369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2049833029838693084574317 768687386189509906715369)
                    ·
                      refine ⟨576515539642132430036527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 768687386189509906715369 576515539642132430036527)
                      ·
                        rfl

theorem cell23_1122760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 3, 1, 3, 2].length) (baseStart_1122760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1122760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1122760 prefixEnd_1122760 := by exact prefixLift 1122760
  have htrace : WordTrace (prefixWord ++ tailWord_1122760) baseStart_1122760 baseEnd_1122760 := by
    simpa [prefixWord, tailWord_1122760, baseEnd_1122760] using wordTrace_append hprefix tailTrace_1122760
  have hstable : (prefixWord ++ tailWord_1122760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122760).length < 2 ^ (prefixWord ++ tailWord_1122760).sum := by decide
  have hdescent : baseEnd_1122760 < baseStart_1122760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122914 : List Nat := [3, 3, 2, 3, 1, 2, 1, 1, 2, 1, 4]
def baseStart_1122914 : Nat := 118140960795 + 1122914 * 2 ^ 59
def prefixEnd_1122914 : Nat := 4983230072969 + 3 ^ 40 * 1122914 * 2
def baseEnd_1122914 : Nat := 576594615662924827510819

theorem tailTrace_1122914 : CollatzResearch.WordTrace tailWord_1122914 prefixEnd_1122914 576594615662924827510819 := by
  unfold tailWord_1122914
  simp only [CollatzResearch.WordTrace]
  refine ⟨10239009563470457822011949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27304025502587887525365197 10239009563470457822011949)
  ·
    refine ⟨3839628586301421683254481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10239009563470457822011949 3839628586301421683254481)
    ·
      refine ⟨2879721439726066262440861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3839628586301421683254481 2879721439726066262440861)
      ·
        refine ⟨1079895539897274848415323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2879721439726066262440861 1079895539897274848415323)
        ·
          refine ⟨1619843309845912272622985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1079895539897274848415323 1619843309845912272622985)
          ·
            refine ⟨1214882482384434204467239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1619843309845912272622985 1214882482384434204467239)
            ·
              refine ⟨1822323723576651306700859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1214882482384434204467239 1822323723576651306700859)
              ·
                refine ⟨2733485585364976960051289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1822323723576651306700859 2733485585364976960051289)
                ·
                  refine ⟨2050114189023732720038467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2733485585364976960051289 2050114189023732720038467)
                  ·
                    refine ⟨3075171283535599080057701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2050114189023732720038467 3075171283535599080057701)
                    ·
                      refine ⟨576594615662924827510819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3075171283535599080057701 576594615662924827510819)
                      ·
                        rfl

theorem cell23_1122914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_1122914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1122914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1122914 prefixEnd_1122914 := by exact prefixLift 1122914
  have htrace : WordTrace (prefixWord ++ tailWord_1122914) baseStart_1122914 baseEnd_1122914 := by
    simpa [prefixWord, tailWord_1122914, baseEnd_1122914] using wordTrace_append hprefix tailTrace_1122914
  have hstable : (prefixWord ++ tailWord_1122914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122914).length < 2 ^ (prefixWord ++ tailWord_1122914).sum := by decide
  have hdescent : baseEnd_1122914 < baseStart_1122914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122917 : List Nat := [1, 3, 1, 3, 4, 2, 1, 1, 2, 2, 3]
def baseStart_1122917 : Nat := 118140960795 + 1122917 * 2 ^ 59
def prefixEnd_1122917 : Nat := 4983230072969 + 3 ^ 40 * 1122917 * 2
def baseEnd_1122917 : Nat := 576596156104888315773305

theorem tailTrace_1122917 : CollatzResearch.WordTrace tailWord_1122917 prefixEnd_1122917 576596156104888315773305 := by
  unfold tailWord_1122917
  simp only [CollatzResearch.WordTrace]
  refine ⟨40956147672870962800407005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27304098448580641866938003 40956147672870962800407005)
  ·
    refine ⟨15358555377326611050152627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40956147672870962800407005 15358555377326611050152627)
    ·
      refine ⟨23037833065989916575228941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15358555377326611050152627 23037833065989916575228941)
      ·
        refine ⟨8639187399746218715710853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23037833065989916575228941 8639187399746218715710853)
        ·
          refine ⟨1619847637452416009195785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8639187399746218715710853 1619847637452416009195785)
          ·
            refine ⟨1214885728089312006896839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1619847637452416009195785 1214885728089312006896839)
            ·
              refine ⟨1822328592133968010345259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1214885728089312006896839 1822328592133968010345259)
              ·
                refine ⟨2733492888200952015517889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1822328592133968010345259 2733492888200952015517889)
                ·
                  refine ⟨2050119666150714011638417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2733492888200952015517889 2050119666150714011638417)
                  ·
                    refine ⟨1537589749613035508728813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2050119666150714011638417 1537589749613035508728813)
                    ·
                      refine ⟨576596156104888315773305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1537589749613035508728813 576596156104888315773305)
                      ·
                        rfl

theorem cell23_1122917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 1, 2, 2, 3].length) (baseStart_1122917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1122917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1122917 prefixEnd_1122917 := by exact prefixLift 1122917
  have htrace : WordTrace (prefixWord ++ tailWord_1122917) baseStart_1122917 baseEnd_1122917 := by
    simpa [prefixWord, tailWord_1122917, baseEnd_1122917] using wordTrace_append hprefix tailTrace_1122917
  have hstable : (prefixWord ++ tailWord_1122917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122917).length < 2 ^ (prefixWord ++ tailWord_1122917).sum := by decide
  have hdescent : baseEnd_1122917 < baseStart_1122917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122940 : List Nat := [2, 2, 2, 1, 1, 2, 2, 4, 2, 3, 2]
def baseStart_1122940 : Nat := 118140960795 + 1122940 * 2 ^ 59
def prefixEnd_1122940 : Nat := 4983230072969 + 3 ^ 40 * 1122940 * 2
def baseEnd_1122940 : Nat := 576607966159941725785699

theorem tailTrace_1122940 : CollatzResearch.WordTrace tailWord_1122940 prefixEnd_1122940 576607966159941725785699 := by
  unfold tailWord_1122940
  simp only [CollatzResearch.WordTrace]
  refine ⟨20478493275893818864247137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27304657701191758485662849 20478493275893818864247137)
  ·
    refine ⟨15358869956920364148185353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20478493275893818864247137 15358869956920364148185353)
    ·
      refine ⟨11519152467690273111139015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15358869956920364148185353 11519152467690273111139015)
      ·
        refine ⟨17278728701535409666708523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11519152467690273111139015 17278728701535409666708523)
        ·
          refine ⟨25918093052303114500062785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17278728701535409666708523 25918093052303114500062785)
          ·
            refine ⟨19438569789227335875047089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25918093052303114500062785 19438569789227335875047089)
            ·
              refine ⟨14578927341920501906285317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19438569789227335875047089 14578927341920501906285317)
              ·
                refine ⟨2733548876610094107428497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14578927341920501906285317 2733548876610094107428497)
                ·
                  refine ⟨2050161657457570580571373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2733548876610094107428497 2050161657457570580571373)
                  ·
                    refine ⟨768810621546588967714265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2050161657457570580571373 768810621546588967714265)
                    ·
                      refine ⟨576607966159941725785699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 768810621546588967714265 576607966159941725785699)
                      ·
                        rfl

theorem cell23_1122940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 4, 2, 3, 2].length) (baseStart_1122940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1122940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1122940 prefixEnd_1122940 := by exact prefixLift 1122940
  have htrace : WordTrace (prefixWord ++ tailWord_1122940) baseStart_1122940 baseEnd_1122940 := by
    simpa [prefixWord, tailWord_1122940, baseEnd_1122940] using wordTrace_append hprefix tailTrace_1122940
  have hstable : (prefixWord ++ tailWord_1122940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122940).length < 2 ^ (prefixWord ++ tailWord_1122940).sum := by decide
  have hdescent : baseEnd_1122940 < baseStart_1122940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122947 : List Nat := [1, 1, 1, 3, 3, 1, 4, 4, 1, 1, 3]
def baseStart_1122947 : Nat := 118140960795 + 1122947 * 2 ^ 59
def prefixEnd_1122947 : Nat := 4983230072969 + 3 ^ 40 * 1122947 * 2
def baseEnd_1122947 : Nat := 576611560524523198398167

theorem tailTrace_1122947 : CollatzResearch.WordTrace tailWord_1122947 prefixEnd_1122947 576611560524523198398167 := by
  unfold tailWord_1122947
  simp only [CollatzResearch.WordTrace]
  refine ⟨40957241862762277923999095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27304827908508185282666063 40957241862762277923999095)
  ·
    refine ⟨61435862794143416885998643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40957241862762277923999095 61435862794143416885998643)
    ·
      refine ⟨92153794191215125328997965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61435862794143416885998643 92153794191215125328997965)
      ·
        refine ⟨34557672821705671998374237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92153794191215125328997965 34557672821705671998374237)
        ·
          refine ⟨12959127308139626999390339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34557672821705671998374237 12959127308139626999390339)
          ·
            refine ⟨19438690962209440499085509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12959127308139626999390339 19438690962209440499085509)
            ·
              refine ⟨3644754555414270093578533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19438690962209440499085509 3644754555414270093578533)
              ·
                refine ⟨683391479140175642545975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3644754555414270093578533 683391479140175642545975)
                ·
                  refine ⟨1025087218710263463818963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 683391479140175642545975 1025087218710263463818963)
                  ·
                    refine ⟨1537630828065395195728445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1025087218710263463818963 1537630828065395195728445)
                    ·
                      refine ⟨576611560524523198398167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1537630828065395195728445 576611560524523198398167)
                      ·
                        rfl

theorem cell23_1122947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 4, 1, 1, 3].length) (baseStart_1122947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1122947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1122947 prefixEnd_1122947 := by exact prefixLift 1122947
  have htrace : WordTrace (prefixWord ++ tailWord_1122947) baseStart_1122947 baseEnd_1122947 := by
    simpa [prefixWord, tailWord_1122947, baseEnd_1122947] using wordTrace_append hprefix tailTrace_1122947
  have hstable : (prefixWord ++ tailWord_1122947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122947).length < 2 ^ (prefixWord ++ tailWord_1122947).sum := by decide
  have hdescent : baseEnd_1122947 < baseStart_1122947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122998 : List Nat := [5, 1, 3, 1, 3, 1, 1, 1, 3, 1, 3]
def baseStart_1122998 : Nat := 118140960795 + 1122998 * 2 ^ 59
def prefixEnd_1122998 : Nat := 4983230072969 + 3 ^ 40 * 1122998 * 2
def baseEnd_1122998 : Nat := 576637748037902498860433

theorem tailTrace_1122998 : CollatzResearch.WordTrace tailWord_1122998 prefixEnd_1122998 576637748037902498860433 := by
  unfold tailWord_1122998
  simp only [CollatzResearch.WordTrace]
  refine ⟨2559943874098594602131603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27306067990385009089403765 2559943874098594602131603)
  ·
    refine ⟨3839915811147891903197405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2559943874098594602131603 3839915811147891903197405)
    ·
      refine ⟨1439968429180459463699027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3839915811147891903197405 1439968429180459463699027)
      ·
        refine ⟨2159952643770689195548541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1439968429180459463699027 2159952643770689195548541)
        ·
          refine ⟨809982241414008448330703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2159952643770689195548541 809982241414008448330703)
          ·
            refine ⟨1214973362121012672496055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 809982241414008448330703 1214973362121012672496055)
            ·
              refine ⟨1822460043181519008744083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1214973362121012672496055 1822460043181519008744083)
              ·
                refine ⟨2733690064772278513116125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1822460043181519008744083 2733690064772278513116125)
                ·
                  refine ⟨1025133774289604442418547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2733690064772278513116125 1025133774289604442418547)
                  ·
                    refine ⟨1537700661434406663627821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1025133774289604442418547 1537700661434406663627821)
                    ·
                      refine ⟨576637748037902498860433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1537700661434406663627821 576637748037902498860433)
                      ·
                        rfl

theorem cell23_1122998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_1122998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1122998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1122998 prefixEnd_1122998 := by exact prefixLift 1122998
  have htrace : WordTrace (prefixWord ++ tailWord_1122998) baseStart_1122998 baseEnd_1122998 := by
    simpa [prefixWord, tailWord_1122998, baseEnd_1122998] using wordTrace_append hprefix tailTrace_1122998
  have hstable : (prefixWord ++ tailWord_1122998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122998).length < 2 ^ (prefixWord ++ tailWord_1122998).sum := by decide
  have hdescent : baseEnd_1122998 < baseStart_1122998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123021 : List Nat := [1, 6, 2, 1, 2, 2, 1, 2, 1, 1, 4]
def baseStart_1123021 : Nat := 118140960795 + 1123021 * 2 ^ 59
def prefixEnd_1123021 : Nat := 4983230072969 + 3 ^ 40 * 1123021 * 2
def baseEnd_1123021 : Nat := 576649558092955908872827

theorem tailTrace_1123021 : CollatzResearch.WordTrace tailWord_1123021 prefixEnd_1123021 576649558092955908872827 := by
  unfold tailWord_1123021
  simp only [CollatzResearch.WordTrace]
  refine ⟨40959940864494188562192917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27306627242996125708128611 40959940864494188562192917)
  ·
    refine ⟨1919997228023165088852793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 40959940864494188562192917 1919997228023165088852793)
    ·
      refine ⟨1439997921017373816639595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1919997228023165088852793 1439997921017373816639595)
      ·
        refine ⟨2159996881526060724959393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1439997921017373816639595 2159996881526060724959393)
        ·
          refine ⟨1619997661144545543719545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2159996881526060724959393 1619997661144545543719545)
          ·
            refine ⟨1214998245858409157789659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1619997661144545543719545 1214998245858409157789659)
            ·
              refine ⟨1822497368787613736684489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1214998245858409157789659 1822497368787613736684489)
              ·
                refine ⟨1366873026590710302513367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1822497368787613736684489 1366873026590710302513367)
                ·
                  refine ⟨2050309539886065453770051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1366873026590710302513367 2050309539886065453770051)
                  ·
                    refine ⟨3075464309829098180655077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2050309539886065453770051 3075464309829098180655077)
                    ·
                      refine ⟨576649558092955908872827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3075464309829098180655077 576649558092955908872827)
                      ·
                        rfl

theorem cell23_1123021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_1123021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1123021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1123021 prefixEnd_1123021 := by exact prefixLift 1123021
  have htrace : WordTrace (prefixWord ++ tailWord_1123021) baseStart_1123021 baseEnd_1123021 := by
    simpa [prefixWord, tailWord_1123021, baseEnd_1123021] using wordTrace_append hprefix tailTrace_1123021
  have hstable : (prefixWord ++ tailWord_1123021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123021).length < 2 ^ (prefixWord ++ tailWord_1123021).sum := by decide
  have hdescent : baseEnd_1123021 < baseStart_1123021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123054 : List Nat := [4, 1, 2, 1, 1, 4, 2, 2, 2, 1, 3]
def baseStart_1123054 : Nat := 118140960795 + 1123054 * 2 ^ 59
def prefixEnd_1123054 : Nat := 4983230072969 + 3 ^ 40 * 1123054 * 2
def baseEnd_1123054 : Nat := 576666502954554279760175

theorem tailTrace_1123054 : CollatzResearch.WordTrace tailWord_1123054 prefixEnd_1123054 576666502954554279760175 := by
  unfold tailWord_1123054
  simp only [CollatzResearch.WordTrace]
  refine ⟨5120143059171829399768027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27307429648916423465429477 5120143059171829399768027)
  ·
    refine ⟨7680214588757744099652041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5120143059171829399768027 7680214588757744099652041)
    ·
      refine ⟨5760160941568308074739031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7680214588757744099652041 5760160941568308074739031)
      ·
        refine ⟨8640241412352462112108547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5760160941568308074739031 8640241412352462112108547)
        ·
          refine ⟨12960362118528693168162821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8640241412352462112108547 12960362118528693168162821)
          ·
            refine ⟨2430067897224129969030529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12960362118528693168162821 2430067897224129969030529)
            ·
              refine ⟨1822550922918097476772897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2430067897224129969030529 1822550922918097476772897)
              ·
                refine ⟨1366913192188573107579673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1822550922918097476772897 1366913192188573107579673)
                ·
                  refine ⟨1025184894141429830684755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1366913192188573107579673 1025184894141429830684755)
                  ·
                    refine ⟨1537777341212144746027133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1025184894141429830684755 1537777341212144746027133)
                    ·
                      refine ⟨576666502954554279760175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1537777341212144746027133 576666502954554279760175)
                      ·
                        rfl

theorem cell23_1123054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 2, 2, 1, 3].length) (baseStart_1123054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1123054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1123054 prefixEnd_1123054 := by exact prefixLift 1123054
  have htrace : WordTrace (prefixWord ++ tailWord_1123054) baseStart_1123054 baseEnd_1123054 := by
    simpa [prefixWord, tailWord_1123054, baseEnd_1123054] using wordTrace_append hprefix tailTrace_1123054
  have hstable : (prefixWord ++ tailWord_1123054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123054).length < 2 ^ (prefixWord ++ tailWord_1123054).sum := by decide
  have hdescent : baseEnd_1123054 < baseStart_1123054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123061 : List Nat := [1, 3, 6, 1, 2, 1, 1, 8]
def baseStart_1123061 : Nat := 118140960795 + 1123061 * 2 ^ 59
def prefixEnd_1123061 : Nat := 4983230072969 + 3 ^ 40 * 1123061 * 2
def baseEnd_1123061 : Nat := 21358151752560583421209

theorem tailTrace_1123061 : CollatzResearch.WordTrace tailWord_1123061 prefixEnd_1123061 21358151752560583421209 := by
  unfold tailWord_1123061
  simp only [CollatzResearch.WordTrace]
  refine ⟨40961399784349275393649037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27307599856232850262432691 40961399784349275393649037)
  ·
    refine ⟨15360524919130978272618389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40961399784349275393649037 15360524919130978272618389)
    ·
      refine ⟨720024605584264606528987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 15360524919130978272618389 720024605584264606528987)
      ·
        refine ⟨1080036908376396909793481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 720024605584264606528987 1080036908376396909793481)
        ·
          refine ⟨810027681282297682345111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1080036908376396909793481 810027681282297682345111)
          ·
            refine ⟨1215041521923446523517667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 810027681282297682345111 1215041521923446523517667)
            ·
              refine ⟨1822562282885169785276501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1215041521923446523517667 1822562282885169785276501)
              ·
                refine ⟨21358151752560583421209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1822562282885169785276501 21358151752560583421209)
                ·
                  rfl

theorem cell23_1123061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 8].length) (baseStart_1123061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1123061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1123061 prefixEnd_1123061 := by exact prefixLift 1123061
  have htrace : WordTrace (prefixWord ++ tailWord_1123061) baseStart_1123061 baseEnd_1123061 := by
    simpa [prefixWord, tailWord_1123061, baseEnd_1123061] using wordTrace_append hprefix tailTrace_1123061
  have hstable : (prefixWord ++ tailWord_1123061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123061).length < 2 ^ (prefixWord ++ tailWord_1123061).sum := by decide
  have hdescent : baseEnd_1123061 < baseStart_1123061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123070 : List Nat := [4, 2, 2, 1, 2, 1, 1, 1, 1, 8]
def baseStart_1123070 : Nat := 118140960795 + 1123070 * 2 ^ 59
def prefixEnd_1123070 : Nat := 4983230072969 + 3 ^ 40 * 1123070 * 2
def baseEnd_1123070 : Nat := 192224906215008739053367

theorem tailTrace_1123070 : CollatzResearch.WordTrace tailWord_1123070 prefixEnd_1123070 192224906215008739053367 := by
  unfold tailWord_1123070
  simp only [CollatzResearch.WordTrace]
  refine ⟨5120216005164583741340833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27307818694211113287151109 5120216005164583741340833)
  ·
    refine ⟨3840162003873437806005625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5120216005164583741340833 3840162003873437806005625)
    ·
      refine ⟨2880121502905078354504219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3840162003873437806005625 2880121502905078354504219)
      ·
        refine ⟨4320182254357617531756329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2880121502905078354504219 4320182254357617531756329)
        ·
          refine ⟨3240136690768213148817247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4320182254357617531756329 3240136690768213148817247)
          ·
            refine ⟨4860205036152319723225871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3240136690768213148817247 4860205036152319723225871)
            ·
              refine ⟨7290307554228479584838807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4860205036152319723225871 7290307554228479584838807)
              ·
                refine ⟨10935461331342719377258211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7290307554228479584838807 10935461331342719377258211)
                ·
                  refine ⟨16403191997014079065887317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10935461331342719377258211 16403191997014079065887317)
                  ·
                    refine ⟨192224906215008739053367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 16403191997014079065887317 192224906215008739053367)
                    ·
                      rfl

theorem cell23_1123070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_1123070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1123070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1123070 prefixEnd_1123070 := by exact prefixLift 1123070
  have htrace : WordTrace (prefixWord ++ tailWord_1123070) baseStart_1123070 baseEnd_1123070 := by
    simpa [prefixWord, tailWord_1123070, baseEnd_1123070] using wordTrace_append hprefix tailTrace_1123070
  have hstable : (prefixWord ++ tailWord_1123070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123070).length < 2 ^ (prefixWord ++ tailWord_1123070).sum := by decide
  have hdescent : baseEnd_1123070 < baseStart_1123070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123120 : List Nat := [2, 1, 1, 1, 2, 2, 1, 3, 1, 7, 2]
def baseStart_1123120 : Nat := 118140960795 + 1123120 * 2 ^ 59
def prefixEnd_1123120 : Nat := 4983230072969 + 3 ^ 40 * 1123120 * 2
def baseEnd_1123120 : Nat := 576700392677751021534871

theorem tailTrace_1123120 : CollatzResearch.WordTrace tailWord_1123120 prefixEnd_1123120 576700392677751021534871 := by
  unfold tailWord_1123120
  simp only [CollatzResearch.WordTrace]
  refine ⟨20481775845567764235023407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27309034460757018980031209 20481775845567764235023407)
  ·
    refine ⟨30722663768351646352535111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20481775845567764235023407 30722663768351646352535111)
    ·
      refine ⟨46083995652527469528802667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30722663768351646352535111 46083995652527469528802667)
      ·
        refine ⟨69125993478791204293204001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46083995652527469528802667 69125993478791204293204001)
        ·
          refine ⟨51844495109093403219903001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69125993478791204293204001 51844495109093403219903001)
          ·
            refine ⟨38883371331820052414927251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51844495109093403219903001 38883371331820052414927251)
            ·
              refine ⟨58325056997730078622390877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38883371331820052414927251 58325056997730078622390877)
              ·
                refine ⟨21871896374148779483396579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58325056997730078622390877 21871896374148779483396579)
                ·
                  refine ⟨32807844561223169225094869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21871896374148779483396579 32807844561223169225094869)
                  ·
                    refine ⟨768933856903668028713161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32807844561223169225094869 768933856903668028713161)
                    ·
                      refine ⟨576700392677751021534871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 768933856903668028713161 576700392677751021534871)
                      ·
                        rfl

theorem cell23_1123120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 1, 7, 2].length) (baseStart_1123120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1123120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1123120 prefixEnd_1123120 := by exact prefixLift 1123120
  have htrace : WordTrace (prefixWord ++ tailWord_1123120) baseStart_1123120 baseEnd_1123120 := by
    simpa [prefixWord, tailWord_1123120, baseEnd_1123120] using wordTrace_append hprefix tailTrace_1123120
  have hstable : (prefixWord ++ tailWord_1123120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123120).length < 2 ^ (prefixWord ++ tailWord_1123120).sum := by decide
  have hdescent : baseEnd_1123120 < baseStart_1123120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123143 : List Nat := [1, 1, 4, 1, 2, 1, 1, 1, 1, 10]
def baseStart_1123143 : Nat := 118140960795 + 1123143 * 2 ^ 59
def prefixEnd_1123143 : Nat := 4983230072969 + 3 ^ 40 * 1123143 * 2
def baseEnd_1123143 : Nat := 192237400910934810515755

theorem tailTrace_1123143 : CollatzResearch.WordTrace tailWord_1123143 prefixEnd_1123143 192237400910934810515755 := by
  unfold tailWord_1123143
  simp only [CollatzResearch.WordTrace]
  refine ⟨40964390570052203398134083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27309593713368135598756055 40964390570052203398134083)
  ·
    refine ⟨61446585855078305097201125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40964390570052203398134083 61446585855078305097201125)
    ·
      refine ⟨11521234847827182205725211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61446585855078305097201125 11521234847827182205725211)
      ·
        refine ⟨17281852271740773308587817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11521234847827182205725211 17281852271740773308587817)
        ·
          refine ⟨12961389203805579981440863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17281852271740773308587817 12961389203805579981440863)
          ·
            refine ⟨19442083805708369972161295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12961389203805579981440863 19442083805708369972161295)
            ·
              refine ⟨29163125708562554958241943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19442083805708369972161295 29163125708562554958241943)
              ·
                refine ⟨43744688562843832437362915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29163125708562554958241943 43744688562843832437362915)
                ·
                  refine ⟨65617032844265748656044373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43744688562843832437362915 65617032844265748656044373)
                  ·
                    refine ⟨192237400910934810515755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 65617032844265748656044373 192237400910934810515755)
                    ·
                      rfl

theorem cell23_1123143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 10].length) (baseStart_1123143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1123143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1123143 prefixEnd_1123143 := by exact prefixLift 1123143
  have htrace : WordTrace (prefixWord ++ tailWord_1123143) baseStart_1123143 baseEnd_1123143 := by
    simpa [prefixWord, tailWord_1123143, baseEnd_1123143] using wordTrace_append hprefix tailTrace_1123143
  have hstable : (prefixWord ++ tailWord_1123143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123143).length < 2 ^ (prefixWord ++ tailWord_1123143).sum := by decide
  have hdescent : baseEnd_1123143 < baseStart_1123143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123150 : List Nat := [4, 1, 1, 1, 1, 1, 1, 2, 6, 1, 4]
def baseStart_1123150 : Nat := 118140960795 + 1123150 * 2 ^ 59
def prefixEnd_1123150 : Nat := 4983230072969 + 3 ^ 40 * 1123150 * 2
def baseEnd_1123150 : Nat := 576715797097385904159733

theorem tailTrace_1123150 : CollatzResearch.WordTrace tailWord_1123150 prefixEnd_1123150 576715797097385904159733 := by
  unfold tailWord_1123150
  simp only [CollatzResearch.WordTrace]
  refine ⟨5120580735128355449204863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27309763920684562395759269 5120580735128355449204863)
  ·
    refine ⟨7680871102692533173807295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5120580735128355449204863 7680871102692533173807295)
    ·
      refine ⟨11521306654038799760710943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7680871102692533173807295 11521306654038799760710943)
      ·
        refine ⟨17281959981058199641066415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11521306654038799760710943 17281959981058199641066415)
        ·
          refine ⟨25922939971587299461599623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17281959981058199641066415 25922939971587299461599623)
          ·
            refine ⟨38884409957380949192399435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25922939971587299461599623 38884409957380949192399435)
            ·
              refine ⟨58326614936071423788599153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38884409957380949192399435 58326614936071423788599153)
              ·
                refine ⟨43744961202053567841449365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58326614936071423788599153 43744961202053567841449365)
                ·
                  refine ⟨2050545056346260992567939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 43744961202053567841449365 2050545056346260992567939)
                  ·
                    refine ⟨3075817584519391488851909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2050545056346260992567939 3075817584519391488851909)
                    ·
                      refine ⟨576715797097385904159733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3075817584519391488851909 576715797097385904159733)
                      ·
                        rfl

theorem cell23_1123150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 6, 1, 4].length) (baseStart_1123150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1123150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1123150 prefixEnd_1123150 := by exact prefixLift 1123150
  have htrace : WordTrace (prefixWord ++ tailWord_1123150) baseStart_1123150 baseEnd_1123150 := by
    simpa [prefixWord, tailWord_1123150, baseEnd_1123150] using wordTrace_append hprefix tailTrace_1123150
  have hstable : (prefixWord ++ tailWord_1123150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123150).length < 2 ^ (prefixWord ++ tailWord_1123150).sum := by decide
  have hdescent : baseEnd_1123150 < baseStart_1123150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123160 : List Nat := [2, 1, 2, 2, 1, 1, 1, 4, 5, 4]
def baseStart_1123160 : Nat := 118140960795 + 1123160 * 2 ^ 59
def prefixEnd_1123160 : Nat := 4983230072969 + 3 ^ 40 * 1123160 * 2
def baseEnd_1123160 : Nat := 192240310634643621678229

theorem tailTrace_1123160 : CollatzResearch.WordTrace tailWord_1123160 prefixEnd_1123160 192240310634643621678229 := by
  unfold tailWord_1123160
  simp only [CollatzResearch.WordTrace]
  refine ⟨20482505305495307650751467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27310007073993743534335289 20482505305495307650751467)
  ·
    refine ⟨30723757958242961476127201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20482505305495307650751467 30723757958242961476127201)
    ·
      refine ⟨23042818468682221107095401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30723757958242961476127201 23042818468682221107095401)
      ·
        refine ⟨17282113851511665830321551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23042818468682221107095401 17282113851511665830321551)
        ·
          refine ⟨25923170777267498745482327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17282113851511665830321551 25923170777267498745482327)
          ·
            refine ⟨38884756165901248118223491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25923170777267498745482327 38884756165901248118223491)
            ·
              refine ⟨58327134248851872177335237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38884756165901248118223491 58327134248851872177335237)
              ·
                refine ⟨10936337671659726033250357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58327134248851872177335237 10936337671659726033250357)
                ·
                  refine ⟨1025281656718099315617221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10936337671659726033250357 1025281656718099315617221)
                  ·
                    refine ⟨192240310634643621678229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1025281656718099315617221 192240310634643621678229)
                    ·
                      rfl

theorem cell23_1123160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 5, 4].length) (baseStart_1123160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1123160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1123160 prefixEnd_1123160 := by exact prefixLift 1123160
  have htrace : WordTrace (prefixWord ++ tailWord_1123160) baseStart_1123160 baseEnd_1123160 := by
    simpa [prefixWord, tailWord_1123160, baseEnd_1123160] using wordTrace_append hprefix tailTrace_1123160
  have hstable : (prefixWord ++ tailWord_1123160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123160).length < 2 ^ (prefixWord ++ tailWord_1123160).sum := by decide
  have hdescent : baseEnd_1123160 < baseStart_1123160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123163 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 6]
def baseStart_1123163 : Nat := 118140960795 + 1123163 * 2 ^ 59
def prefixEnd_1123163 : Nat := 4983230072969 + 3 ^ 40 * 1123163 * 2
def baseEnd_1123163 : Nat := 576722472345894353297173

theorem tailTrace_1123163 : CollatzResearch.WordTrace tailWord_1123163 prefixEnd_1123163 576722472345894353297173 := by
  unfold tailWord_1123163
  simp only [CollatzResearch.WordTrace]
  refine ⟨40965120029979746813862143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27310080019986497875908095 40965120029979746813862143)
  ·
    refine ⟨61447680044969620220793215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40965120029979746813862143 61447680044969620220793215)
    ·
      refine ⟨92171520067454430331189823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61447680044969620220793215 92171520067454430331189823)
      ·
        refine ⟨138257280101181645496784735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92171520067454430331189823 138257280101181645496784735)
        ·
          refine ⟨207385920151772468245177103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138257280101181645496784735 207385920151772468245177103)
          ·
            refine ⟨311078880227658702367765655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207385920151772468245177103 311078880227658702367765655)
            ·
              refine ⟨466618320341488053551648483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 311078880227658702367765655 466618320341488053551648483)
              ·
                refine ⟨699927480512232080327472725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 466618320341488053551648483 699927480512232080327472725)
                ·
                  refine ⟨8202275162252719691337571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 699927480512232080327472725 8202275162252719691337571)
                  ·
                    refine ⟨12303412743379079537006357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8202275162252719691337571 12303412743379079537006357)
                    ·
                      refine ⟨576722472345894353297173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12303412743379079537006357 576722472345894353297173)
                      ·
                        rfl

theorem cell23_1123163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 6].length) (baseStart_1123163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1123163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1123163 prefixEnd_1123163 := by exact prefixLift 1123163
  have htrace : WordTrace (prefixWord ++ tailWord_1123163) baseStart_1123163 baseEnd_1123163 := by
    simpa [prefixWord, tailWord_1123163, baseEnd_1123163] using wordTrace_append hprefix tailTrace_1123163
  have hstable : (prefixWord ++ tailWord_1123163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123163).length < 2 ^ (prefixWord ++ tailWord_1123163).sum := by decide
  have hdescent : baseEnd_1123163 < baseStart_1123163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123257 : List Nat := [1, 2, 1, 4, 2, 2, 2, 1, 3, 1, 4]
def baseStart_1123257 : Nat := 118140960795 + 1123257 * 2 ^ 59
def prefixEnd_1123257 : Nat := 4983230072969 + 3 ^ 40 * 1123257 * 2
def baseEnd_1123257 : Nat := 576770739527416985521741

theorem tailTrace_1123257 : CollatzResearch.WordTrace tailWord_1123257 prefixEnd_1123257 576770739527416985521741 := by
  unfold tailWord_1123257
  simp only [CollatzResearch.WordTrace]
  refine ⟨40968548491639200867784025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27312365661092800578522683 40968548491639200867784025)
  ·
    refine ⟨30726411368729400650838019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40968548491639200867784025 30726411368729400650838019)
    ·
      refine ⟨46089617053094100976257029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30726411368729400650838019 46089617053094100976257029)
      ·
        refine ⟨8641803197455143933048193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46089617053094100976257029 8641803197455143933048193)
        ·
          refine ⟨6481352398091357949786145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8641803197455143933048193 6481352398091357949786145)
          ·
            refine ⟨4861014298568518462339609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6481352398091357949786145 4861014298568518462339609)
            ·
              refine ⟨3645760723926388846754707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4861014298568518462339609 3645760723926388846754707)
              ·
                refine ⟨5468641085889583270132061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3645760723926388846754707 5468641085889583270132061)
                ·
                  refine ⟨2050740407208593726299523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5468641085889583270132061 2050740407208593726299523)
                  ·
                    refine ⟨3076110610812890589449285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2050740407208593726299523 3076110610812890589449285)
                    ·
                      refine ⟨576770739527416985521741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3076110610812890589449285 576770739527416985521741)
                      ·
                        rfl

theorem cell23_1123257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_1123257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1123257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1123257 prefixEnd_1123257 := by exact prefixLift 1123257
  have htrace : WordTrace (prefixWord ++ tailWord_1123257) baseStart_1123257 baseEnd_1123257 := by
    simpa [prefixWord, tailWord_1123257, baseEnd_1123257] using wordTrace_append hprefix tailTrace_1123257
  have hstable : (prefixWord ++ tailWord_1123257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123257).length < 2 ^ (prefixWord ++ tailWord_1123257).sum := by decide
  have hdescent : baseEnd_1123257 < baseStart_1123257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123274 : List Nat := [3, 1, 2, 1, 2, 1, 1, 1, 7, 2, 2]
def baseStart_1123274 : Nat := 118140960795 + 1123274 * 2 ^ 59
def prefixEnd_1123274 : Nat := 4983230072969 + 3 ^ 40 * 1123274 * 2
def baseEnd_1123274 : Nat := 576779468698543419009163

theorem tailTrace_1123274 : CollatzResearch.WordTrace tailWord_1123274 prefixEnd_1123274 576779468698543419009163 := by
  unfold tailWord_1123274
  simp only [CollatzResearch.WordTrace]
  refine ⟨10242292133144403192788219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27312779021718408514101917 10242292133144403192788219)
  ·
    refine ⟨15363438199716604789182329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10242292133144403192788219 15363438199716604789182329)
    ·
      refine ⟨11522578649787453591886747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15363438199716604789182329 11522578649787453591886747)
      ·
        refine ⟨17283867974681180387830121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11522578649787453591886747 17283867974681180387830121)
        ·
          refine ⟨12962900981010885290872591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17283867974681180387830121 12962900981010885290872591)
          ·
            refine ⟨19444351471516327936308887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12962900981010885290872591 19444351471516327936308887)
            ·
              refine ⟨29166527207274491904463331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19444351471516327936308887 29166527207274491904463331)
              ·
                refine ⟨43749790810911737856694997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29166527207274491904463331 43749790810911737856694997)
                ·
                  refine ⟨1025385722130743856016289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 43749790810911737856694997 1025385722130743856016289)
                  ·
                    refine ⟨769039291598057892012217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1025385722130743856016289 769039291598057892012217)
                    ·
                      refine ⟨576779468698543419009163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 769039291598057892012217 576779468698543419009163)
                      ·
                        rfl

theorem cell23_1123274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 7, 2, 2].length) (baseStart_1123274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1123274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1123274 prefixEnd_1123274 := by exact prefixLift 1123274
  have htrace : WordTrace (prefixWord ++ tailWord_1123274) baseStart_1123274 baseEnd_1123274 := by
    simpa [prefixWord, tailWord_1123274, baseEnd_1123274] using wordTrace_append hprefix tailTrace_1123274
  have hstable : (prefixWord ++ tailWord_1123274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123274).length < 2 ^ (prefixWord ++ tailWord_1123274).sum := by decide
  have hdescent : baseEnd_1123274 < baseStart_1123274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123284 : List Nat := [2, 4, 1, 2, 1, 3, 1, 1, 4, 4]
def baseStart_1123284 : Nat := 118140960795 + 1123284 * 2 ^ 59
def prefixEnd_1123284 : Nat := 4983230072969 + 3 ^ 40 * 1123284 * 2
def baseEnd_1123284 : Nat := 192261534501696126628039

theorem tailTrace_1123284 : CollatzResearch.WordTrace tailWord_1123284 prefixEnd_1123284 192261534501696126628039 := by
  unfold tailWord_1123284
  simp only [CollatzResearch.WordTrace]
  refine ⟨20484766631270692239508453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27313022175027589652677937 20484766631270692239508453)
  ·
    refine ⟨3840893743363254794907835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20484766631270692239508453 3840893743363254794907835)
    ·
      refine ⟨5761340615044882192361753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3840893743363254794907835 5761340615044882192361753)
      ·
        refine ⟨4321005461283661644271315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5761340615044882192361753 4321005461283661644271315)
        ·
          refine ⟨6481508191925492466406973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4321005461283661644271315 6481508191925492466406973)
          ·
            refine ⟨2430565571972059674902615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6481508191925492466406973 2430565571972059674902615)
            ·
              refine ⟨3645848357958089512353923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2430565571972059674902615 3645848357958089512353923)
              ·
                refine ⟨5468772536937134268530885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3645848357958089512353923 5468772536937134268530885)
                ·
                  refine ⟨1025394850675712675349541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5468772536937134268530885 1025394850675712675349541)
                  ·
                    refine ⟨192261534501696126628039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1025394850675712675349541 192261534501696126628039)
                    ·
                      rfl

theorem cell23_1123284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 4, 4].length) (baseStart_1123284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1123284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1123284 prefixEnd_1123284 := by exact prefixLift 1123284
  have htrace : WordTrace (prefixWord ++ tailWord_1123284) baseStart_1123284 baseEnd_1123284 := by
    simpa [prefixWord, tailWord_1123284, baseEnd_1123284] using wordTrace_append hprefix tailTrace_1123284
  have hstable : (prefixWord ++ tailWord_1123284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123284).length < 2 ^ (prefixWord ++ tailWord_1123284).sum := by decide
  have hdescent : baseEnd_1123284 < baseStart_1123284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123300 : List Nat := [2, 3, 1, 1, 1, 1, 2, 1, 1, 4, 6]
def baseStart_1123300 : Nat := 118140960795 + 1123300 * 2 ^ 59
def prefixEnd_1123300 : Nat := 4983230072969 + 3 ^ 40 * 1123300 * 2
def baseEnd_1123300 : Nat := 576792819195560317284043

theorem tailTrace_1123300 : CollatzResearch.WordTrace tailWord_1123300 prefixEnd_1123300 576792819195560317284043 := by
  unfold tailWord_1123300
  simp only [CollatzResearch.WordTrace]
  refine ⟨20485058415241709605799677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27313411220322279474399569 20485058415241709605799677)
  ·
    refine ⟨7681896905715641102174879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20485058415241709605799677 7681896905715641102174879)
    ·
      refine ⟨11522845358573461653262319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7681896905715641102174879 11522845358573461653262319)
      ·
        refine ⟨17284268037860192479893479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11522845358573461653262319 17284268037860192479893479)
        ·
          refine ⟨25926402056790288719840219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17284268037860192479893479 25926402056790288719840219)
          ·
            refine ⟨38889603085185433079760329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25926402056790288719840219 38889603085185433079760329)
            ·
              refine ⟨29167202313889074809820247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38889603085185433079760329 29167202313889074809820247)
              ·
                refine ⟨43750803470833612214730371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29167202313889074809820247 43750803470833612214730371)
                ·
                  refine ⟨65626205206250418322095557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43750803470833612214730371 65626205206250418322095557)
                  ·
                    refine ⟨12304913476171953435392917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 65626205206250418322095557 12304913476171953435392917)
                    ·
                      refine ⟨576792819195560317284043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12304913476171953435392917 576792819195560317284043)
                      ·
                        rfl

theorem cell23_1123300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_1123300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1123300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1123300 prefixEnd_1123300 := by exact prefixLift 1123300
  have htrace : WordTrace (prefixWord ++ tailWord_1123300) baseStart_1123300 baseEnd_1123300 := by
    simpa [prefixWord, tailWord_1123300, baseEnd_1123300] using wordTrace_append hprefix tailTrace_1123300
  have hstable : (prefixWord ++ tailWord_1123300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123300).length < 2 ^ (prefixWord ++ tailWord_1123300).sum := by decide
  have hdescent : baseEnd_1123300 < baseStart_1123300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123301 : List Nat := [1, 3, 1, 6, 1, 2, 1, 1, 1, 6]
def baseStart_1123301 : Nat := 118140960795 + 1123301 * 2 ^ 59
def prefixEnd_1123301 : Nat := 4983230072969 + 3 ^ 40 * 1123301 * 2
def baseEnd_1123301 : Nat := 192264444225404937790513

theorem tailTrace_1123301 : CollatzResearch.WordTrace tailWord_1123301 prefixEnd_1123301 192264444225404937790513 := by
  unfold tailWord_1123301
  simp only [CollatzResearch.WordTrace]
  refine ⟨40970153303479796382385757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27313435535653197588257171 40970153303479796382385757)
  ·
    refine ⟨15363807488804923643394659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40970153303479796382385757 15363807488804923643394659)
    ·
      refine ⟨23045711233207385465091989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15363807488804923643394659 23045711233207385465091989)
      ·
        refine ⟨1080267714056596193676187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 23045711233207385465091989 1080267714056596193676187)
        ·
          refine ⟨1620401571084894290514281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1080267714056596193676187 1620401571084894290514281)
          ·
            refine ⟨1215301178313670717885711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1620401571084894290514281 1215301178313670717885711)
            ·
              refine ⟨1822951767470506076828567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1215301178313670717885711 1822951767470506076828567)
              ·
                refine ⟨2734427651205759115242851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1822951767470506076828567 2734427651205759115242851)
                ·
                  refine ⟨4101641476808638672864277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2734427651205759115242851 4101641476808638672864277)
                  ·
                    refine ⟨192264444225404937790513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4101641476808638672864277 192264444225404937790513)
                    ·
                      rfl

theorem cell23_1123301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 1, 1, 6].length) (baseStart_1123301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1123301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1123301 prefixEnd_1123301 := by exact prefixLift 1123301
  have htrace : WordTrace (prefixWord ++ tailWord_1123301) baseStart_1123301 baseEnd_1123301 := by
    simpa [prefixWord, tailWord_1123301, baseEnd_1123301] using wordTrace_append hprefix tailTrace_1123301
  have hstable : (prefixWord ++ tailWord_1123301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123301).length < 2 ^ (prefixWord ++ tailWord_1123301).sum := by decide
  have hdescent : baseEnd_1123301 < baseStart_1123301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123314 : List Nat := [3, 2, 1, 5, 1, 1, 1, 9]
def baseStart_1123314 : Nat := 118140960795 + 1123314 * 2 ^ 59
def prefixEnd_1123314 : Nat := 4983230072969 + 3 ^ 40 * 1123314 * 2
def baseEnd_1123314 : Nat := 21362963256471231944777

theorem tailTrace_1123314 : CollatzResearch.WordTrace tailWord_1123314 prefixEnd_1123314 21362963256471231944777 := by
  unfold tailWord_1123314
  simp only [CollatzResearch.WordTrace]
  refine ⟨10242656863108174900652249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27313751634955133068405997 10242656863108174900652249)
  ·
    refine ⟨7681992647331131175489187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10242656863108174900652249 7681992647331131175489187)
    ·
      refine ⟨11522988970996696763233781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7681992647331131175489187 11522988970996696763233781)
      ·
        refine ⟨1080280216030940321553167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11522988970996696763233781 1080280216030940321553167)
        ·
          refine ⟨1620420324046410482329751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1080280216030940321553167 1620420324046410482329751)
          ·
            refine ⟨2430630486069615723494627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1620420324046410482329751 2430630486069615723494627)
            ·
              refine ⟨3645945729104423585241941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2430630486069615723494627 3645945729104423585241941)
              ·
                refine ⟨21362963256471231944777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3645945729104423585241941 21362963256471231944777)
                ·
                  rfl

theorem cell23_1123314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 9].length) (baseStart_1123314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1123314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1123314 prefixEnd_1123314 := by exact prefixLift 1123314
  have htrace : WordTrace (prefixWord ++ tailWord_1123314) baseStart_1123314 baseEnd_1123314 := by
    simpa [prefixWord, tailWord_1123314, baseEnd_1123314] using wordTrace_append hprefix tailTrace_1123314
  have hstable : (prefixWord ++ tailWord_1123314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123314).length < 2 ^ (prefixWord ++ tailWord_1123314).sum := by decide
  have hdescent : baseEnd_1123314 < baseStart_1123314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123324 : List Nat := [2, 2, 2, 1, 2, 3, 1, 2, 4, 1, 3]
def baseStart_1123324 : Nat := 118140960795 + 1123324 * 2 ^ 59
def prefixEnd_1123324 : Nat := 4983230072969 + 3 ^ 40 * 1123324 * 2
def baseEnd_1123324 : Nat := 576805142731268223383933

theorem tailTrace_1123324 : CollatzResearch.WordTrace tailWord_1123324 prefixEnd_1123324 576805142731268223383933 := by
  unfold tailWord_1123324
  simp only [CollatzResearch.WordTrace]
  refine ⟨20485496091198235655236513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27313994788264314206982017 20485496091198235655236513)
  ·
    refine ⟨15364122068398676741427385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20485496091198235655236513 15364122068398676741427385)
    ·
      refine ⟨11523091551299007556070539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15364122068398676741427385 11523091551299007556070539)
      ·
        refine ⟨17284637326948511334105809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11523091551299007556070539 17284637326948511334105809)
        ·
          refine ⟨12963477995211383500579357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17284637326948511334105809 12963477995211383500579357)
          ·
            refine ⟨4861304248204268812717259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12963477995211383500579357 4861304248204268812717259)
            ·
              refine ⟨7291956372306403219075889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4861304248204268812717259 7291956372306403219075889)
              ·
                refine ⟨5468967279229802414306917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7291956372306403219075889 5468967279229802414306917)
                ·
                  refine ⟨1025431364855587952682547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5468967279229802414306917 1025431364855587952682547)
                  ·
                    refine ⟨1538147047283381929023821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1025431364855587952682547 1538147047283381929023821)
                    ·
                      refine ⟨576805142731268223383933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1538147047283381929023821 576805142731268223383933)
                      ·
                        rfl

theorem cell23_1123324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 4, 1, 3].length) (baseStart_1123324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1123324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1123324 prefixEnd_1123324 := by exact prefixLift 1123324
  have htrace : WordTrace (prefixWord ++ tailWord_1123324) baseStart_1123324 baseEnd_1123324 := by
    simpa [prefixWord, tailWord_1123324, baseEnd_1123324] using wordTrace_append hprefix tailTrace_1123324
  have hstable : (prefixWord ++ tailWord_1123324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123324).length < 2 ^ (prefixWord ++ tailWord_1123324).sum := by decide
  have hdescent : baseEnd_1123324 < baseStart_1123324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123421 : List Nat := [1, 4, 4, 1, 2, 1, 1, 2, 7]
def baseStart_1123421 : Nat := 118140960795 + 1123421 * 2 ^ 59
def prefixEnd_1123421 : Nat := 4983230072969 + 3 ^ 40 * 1123421 * 2
def baseEnd_1123421 : Nat := 64094994483861593763443

theorem tailTrace_1123421 : CollatzResearch.WordTrace tailWord_1123421 prefixEnd_1123421 64094994483861593763443 := by
  unfold tailWord_1123421
  simp only [CollatzResearch.WordTrace]
  refine ⟨40974530063045056876754117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27316353375363371251169411 40974530063045056876754117)
  ·
    refine ⟨7682724386820948164391397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40974530063045056876754117 7682724386820948164391397)
    ·
      refine ⟨1440510822528927780823387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7682724386820948164391397 1440510822528927780823387)
      ·
        refine ⟨2160766233793391671235081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1440510822528927780823387 2160766233793391671235081)
        ·
          refine ⟨1620574675345043753426311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2160766233793391671235081 1620574675345043753426311)
          ·
            refine ⟨2430862013017565630139467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1620574675345043753426311 2430862013017565630139467)
            ·
              refine ⟨3646293019526348445209201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2430862013017565630139467 3646293019526348445209201)
              ·
                refine ⟨2734719764644761333906901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3646293019526348445209201 2734719764644761333906901)
                ·
                  refine ⟨64094994483861593763443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2734719764644761333906901 64094994483861593763443)
                  ·
                    rfl

theorem cell23_1123421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 2, 7].length) (baseStart_1123421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1123421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1123421 prefixEnd_1123421 := by exact prefixLift 1123421
  have htrace : WordTrace (prefixWord ++ tailWord_1123421) baseStart_1123421 baseEnd_1123421 := by
    simpa [prefixWord, tailWord_1123421, baseEnd_1123421] using wordTrace_append hprefix tailTrace_1123421
  have hstable : (prefixWord ++ tailWord_1123421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123421).length < 2 ^ (prefixWord ++ tailWord_1123421).sum := by decide
  have hdescent : baseEnd_1123421 < baseStart_1123421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123424 : List Nat := [2, 1, 1, 3, 2, 2, 1, 2, 2, 5, 2]
def baseStart_1123424 : Nat := 118140960795 + 1123424 * 2 ^ 59
def prefixEnd_1123424 : Nat := 4983230072969 + 3 ^ 40 * 1123424 * 2
def baseEnd_1123424 : Nat := 576856490796717832133473

theorem tailTrace_1123424 : CollatzResearch.WordTrace tailWord_1123424 prefixEnd_1123424 576856490796717832133473 := by
  unfold tailWord_1123424
  simp only [CollatzResearch.WordTrace]
  refine ⟨20487319741017094194556663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27316426321356125592742217 20487319741017094194556663)
  ·
    refine ⟨30730979611525641291834995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20487319741017094194556663 30730979611525641291834995)
    ·
      refine ⟨46096469417288461937752493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30730979611525641291834995 46096469417288461937752493)
      ·
        refine ⟨17286176031483173226657185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46096469417288461937752493 17286176031483173226657185)
        ·
          refine ⟨12964632023612379919992889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17286176031483173226657185 12964632023612379919992889)
          ·
            refine ⟨9723474017709284939994667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12964632023612379919992889 9723474017709284939994667)
            ·
              refine ⟨14585211026563927409992001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9723474017709284939994667 14585211026563927409992001)
              ·
                refine ⟨10938908269922945557494001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14585211026563927409992001 10938908269922945557494001)
                ·
                  refine ⟨8204181202442209168120501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10938908269922945557494001 8204181202442209168120501)
                  ·
                    refine ⟨769141987728957109511297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8204181202442209168120501 769141987728957109511297)
                    ·
                      refine ⟨576856490796717832133473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 769141987728957109511297 576856490796717832133473)
                      ·
                        rfl

theorem cell23_1123424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 2, 5, 2].length) (baseStart_1123424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1123424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1123424 prefixEnd_1123424 := by exact prefixLift 1123424
  have htrace : WordTrace (prefixWord ++ tailWord_1123424) baseStart_1123424 baseEnd_1123424 := by
    simpa [prefixWord, tailWord_1123424, baseEnd_1123424] using wordTrace_append hprefix tailTrace_1123424
  have hstable : (prefixWord ++ tailWord_1123424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123424).length < 2 ^ (prefixWord ++ tailWord_1123424).sum := by decide
  have hdescent : baseEnd_1123424 < baseStart_1123424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123434 : List Nat := [3, 1, 3, 2, 2, 2, 1, 1, 1, 7]
def baseStart_1123434 : Nat := 118140960795 + 1123434 * 2 ^ 59
def prefixEnd_1123434 : Nat := 4983230072969 + 3 ^ 40 * 1123434 * 2
def baseEnd_1123434 : Nat := 192287208534420931002809

theorem tailTrace_1123434 : CollatzResearch.WordTrace tailWord_1123434 prefixEnd_1123434 192287208534420931002809 := by
  unfold tailWord_1123434
  simp only [CollatzResearch.WordTrace]
  refine ⟨10243751052999490024244339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27316669474665306731318237 10243751052999490024244339)
  ·
    refine ⟨15365626579499235036366509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10243751052999490024244339 15365626579499235036366509)
    ·
      refine ⟨5762109967312213138637441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15365626579499235036366509 5762109967312213138637441)
      ·
        refine ⟨4321582475484159853978081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5762109967312213138637441 4321582475484159853978081)
        ·
          refine ⟨3241186856613119890483561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4321582475484159853978081 3241186856613119890483561)
          ·
            refine ⟨2430890142459839917862671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3241186856613119890483561 2430890142459839917862671)
            ·
              refine ⟨3646335213689759876794007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2430890142459839917862671 3646335213689759876794007)
              ·
                refine ⟨5469502820534639815191011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3646335213689759876794007 5469502820534639815191011)
                ·
                  refine ⟨8204254230801959722786517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5469502820534639815191011 8204254230801959722786517)
                  ·
                    refine ⟨192287208534420931002809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8204254230801959722786517 192287208534420931002809)
                    ·
                      rfl

theorem cell23_1123434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 1, 7].length) (baseStart_1123434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1123434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1123434 prefixEnd_1123434 := by exact prefixLift 1123434
  have htrace : WordTrace (prefixWord ++ tailWord_1123434) baseStart_1123434 baseEnd_1123434 := by
    simpa [prefixWord, tailWord_1123434, baseEnd_1123434] using wordTrace_append hprefix tailTrace_1123434
  have hstable : (prefixWord ++ tailWord_1123434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123434).length < 2 ^ (prefixWord ++ tailWord_1123434).sum := by decide
  have hdescent : baseEnd_1123434 < baseStart_1123434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123541 : List Nat := [1, 3, 2, 4, 1, 2, 1, 1, 3, 5]
def baseStart_1123541 : Nat := 118140960795 + 1123541 * 2 ^ 59
def prefixEnd_1123541 : Nat := 4983230072969 + 3 ^ 40 * 1123541 * 2
def baseEnd_1123541 : Nat := 192305522677764624790145

theorem tailTrace_1123541 : CollatzResearch.WordTrace tailWord_1123541 prefixEnd_1123541 192305522677764624790145 := by
  unfold tailWord_1123541
  simp only [CollatzResearch.WordTrace]
  refine ⟨40978906822610317371122477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27319271215073544914081651 40978906822610317371122477)
  ·
    refine ⟨15367090058478869014170929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40978906822610317371122477 15367090058478869014170929)
    ·
      refine ⟨11525317543859151760628197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15367090058478869014170929 11525317543859151760628197)
      ·
        refine ⟨2160997039473590955117787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11525317543859151760628197 2160997039473590955117787)
        ·
          refine ⟨3241495559210386432676681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2160997039473590955117787 3241495559210386432676681)
          ·
            refine ⟨2431121669407789824507511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3241495559210386432676681 2431121669407789824507511)
            ·
              refine ⟨3646682504111684736761267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2431121669407789824507511 3646682504111684736761267)
              ·
                refine ⟨5470023756167527105141901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3646682504111684736761267 5470023756167527105141901)
                ·
                  refine ⟨2051258908562822664428213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5470023756167527105141901 2051258908562822664428213)
                  ·
                    refine ⟨192305522677764624790145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2051258908562822664428213 192305522677764624790145)
                    ·
                      rfl

theorem cell23_1123541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 3, 5].length) (baseStart_1123541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1123541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1123541 prefixEnd_1123541 := by exact prefixLift 1123541
  have htrace : WordTrace (prefixWord ++ tailWord_1123541) baseStart_1123541 baseEnd_1123541 := by
    simpa [prefixWord, tailWord_1123541, baseEnd_1123541] using wordTrace_append hprefix tailTrace_1123541
  have hstable : (prefixWord ++ tailWord_1123541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123541).length < 2 ^ (prefixWord ++ tailWord_1123541).sum := by decide
  have hdescent : baseEnd_1123541 < baseStart_1123541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123567 : List Nat := [1, 1, 2, 1, 18]
def baseStart_1123567 : Nat := 118140960795 + 1123567 * 2 ^ 59
def prefixEnd_1123567 : Nat := 4983230072969 + 3 ^ 40 * 1123567 * 2
def baseEnd_1123567 : Nat := 791399065199328906235

theorem tailTrace_1123567 : CollatzResearch.WordTrace tailWord_1123567 prefixEnd_1123567 791399065199328906235 := by
  unfold tailWord_1123567
  simp only [CollatzResearch.WordTrace]
  refine ⟨40979855120516123811568955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27319903413677415874379303 40979855120516123811568955)
  ·
    refine ⟨61469782680774185717353433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40979855120516123811568955 61469782680774185717353433)
    ·
      refine ⟨46102337010580639288015075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61469782680774185717353433 46102337010580639288015075)
      ·
        refine ⟨69153505515870958932022613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46102337010580639288015075 69153505515870958932022613)
        ·
          refine ⟨791399065199328906235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 18 69153505515870958932022613 791399065199328906235)
          ·
            rfl

theorem cell23_1123567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 18].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 18].length) (baseStart_1123567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1123567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1123567 prefixEnd_1123567 := by exact prefixLift 1123567
  have htrace : WordTrace (prefixWord ++ tailWord_1123567) baseStart_1123567 baseEnd_1123567 := by
    simpa [prefixWord, tailWord_1123567, baseEnd_1123567] using wordTrace_append hprefix tailTrace_1123567
  have hstable : (prefixWord ++ tailWord_1123567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123567).length < 2 ^ (prefixWord ++ tailWord_1123567).sum := by decide
  have hdescent : baseEnd_1123567 < baseStart_1123567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123571 : List Nat := [1, 1, 1, 2, 2, 5, 1, 4, 2, 4]
def baseStart_1123571 : Nat := 118140960795 + 1123571 * 2 ^ 59
def prefixEnd_1123571 : Nat := 4983230072969 + 3 ^ 40 * 1123571 * 2
def baseEnd_1123571 : Nat := 192310657484309585665099

theorem tailTrace_1123571 : CollatzResearch.WordTrace tailWord_1123571 prefixEnd_1123571 192310657484309585665099 := by
  unfold tailWord_1123571
  simp only [CollatzResearch.WordTrace]
  refine ⟨40980001012501632494714567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27320000675001088329809711 40980001012501632494714567)
  ·
    refine ⟨61470001518752448742071851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40980001012501632494714567 61470001518752448742071851)
    ·
      refine ⟨92205002278128673113107777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61470001518752448742071851 92205002278128673113107777)
      ·
        refine ⟨69153751708596504834830833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92205002278128673113107777 69153751708596504834830833)
        ·
          refine ⟨51865313781447378626123125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69153751708596504834830833 51865313781447378626123125)
          ·
            refine ⟨4862373167010691746199043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51865313781447378626123125 4862373167010691746199043)
            ·
              refine ⟨7293559750516037619298565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4862373167010691746199043 7293559750516037619298565)
              ·
                refine ⟨1367542453221757053618481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7293559750516037619298565 1367542453221757053618481)
                ·
                  refine ⟨1025656839916317790213861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1367542453221757053618481 1025656839916317790213861)
                  ·
                    refine ⟨192310657484309585665099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1025656839916317790213861 192310657484309585665099)
                    ·
                      rfl

theorem cell23_1123571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 4, 2, 4].length) (baseStart_1123571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1123571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1123571 prefixEnd_1123571 := by exact prefixLift 1123571
  have htrace : WordTrace (prefixWord ++ tailWord_1123571) baseStart_1123571 baseEnd_1123571 := by
    simpa [prefixWord, tailWord_1123571, baseEnd_1123571] using wordTrace_append hprefix tailTrace_1123571
  have hstable : (prefixWord ++ tailWord_1123571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123571).length < 2 ^ (prefixWord ++ tailWord_1123571).sum := by decide
  have hdescent : baseEnd_1123571 < baseStart_1123571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123578 : List Nat := [3, 1, 1, 1, 1, 4, 2, 3, 3, 2, 2]
def baseStart_1123578 : Nat := 118140960795 + 1123578 * 2 ^ 59
def prefixEnd_1123578 : Nat := 4983230072969 + 3 ^ 40 * 1123578 * 2
def baseEnd_1123578 : Nat := 576935566817510229607765

theorem tailTrace_1123578 : CollatzResearch.WordTrace tailWord_1123578 prefixEnd_1123578 576935566817510229607765 := by
  unfold tailWord_1123578
  simp only [CollatzResearch.WordTrace]
  refine ⟨10245064080869068172554847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27320170882317515126812925 10245064080869068172554847)
  ·
    refine ⟨15367596121303602258832271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10245064080869068172554847 15367596121303602258832271)
    ·
      refine ⟨23051394181955403388248407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15367596121303602258832271 23051394181955403388248407)
      ·
        refine ⟨34577091272933105082372611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23051394181955403388248407 34577091272933105082372611)
        ·
          refine ⟨51865636909399657623558917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34577091272933105082372611 51865636909399657623558917)
          ·
            refine ⟨9724806920512435804417297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51865636909399657623558917 9724806920512435804417297)
            ·
              refine ⟨7293605190384326853312973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9724806920512435804417297 7293605190384326853312973)
              ·
                refine ⟨2735101946394122569992365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7293605190384326853312973 2735101946394122569992365)
                ·
                  refine ⟨1025663229897795963747137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2735101946394122569992365 1025663229897795963747137)
                  ·
                    refine ⟨769247422423346972810353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1025663229897795963747137 769247422423346972810353)
                    ·
                      refine ⟨576935566817510229607765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 769247422423346972810353 576935566817510229607765)
                      ·
                        rfl

theorem cell23_1123578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 3, 3, 2, 2].length) (baseStart_1123578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1123578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1123578 prefixEnd_1123578 := by exact prefixLift 1123578
  have htrace : WordTrace (prefixWord ++ tailWord_1123578) baseStart_1123578 baseEnd_1123578 := by
    simpa [prefixWord, tailWord_1123578, baseEnd_1123578] using wordTrace_append hprefix tailTrace_1123578
  have hstable : (prefixWord ++ tailWord_1123578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123578).length < 2 ^ (prefixWord ++ tailWord_1123578).sum := by decide
  have hdescent : baseEnd_1123578 < baseStart_1123578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123588 : List Nat := [2, 3, 2, 2, 2, 1, 2, 3, 2, 4]
def baseStart_1123588 : Nat := 118140960795 + 1123588 * 2 ^ 59
def prefixEnd_1123588 : Nat := 4983230072969 + 3 ^ 40 * 1123588 * 2
def baseEnd_1123588 : Nat := 192313567208018396827573

theorem tailTrace_1123588 : CollatzResearch.WordTrace tailWord_1123588 prefixEnd_1123588 192313567208018396827573 := by
  unfold tailWord_1123588
  simp only [CollatzResearch.WordTrace]
  refine ⟨20490310526720022199041709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27320414035626696265388945 20490310526720022199041709)
  ·
    refine ⟨7683866447520008324640641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20490310526720022199041709 7683866447520008324640641)
    ·
      refine ⟨5762899835640006243480481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7683866447520008324640641 5762899835640006243480481)
      ·
        refine ⟨4322174876730004682610361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5762899835640006243480481 4322174876730004682610361)
        ·
          refine ⟨3241631157547503511957771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4322174876730004682610361 3241631157547503511957771)
          ·
            refine ⟨4862446736321255267936657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3241631157547503511957771 4862446736321255267936657)
            ·
              refine ⟨3646835052240941450952493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4862446736321255267936657 3646835052240941450952493)
              ·
                refine ⟨1367563144590353044107185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3646835052240941450952493 1367563144590353044107185)
                ·
                  refine ⟨1025672358442764783080389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1367563144590353044107185 1025672358442764783080389)
                  ·
                    refine ⟨192313567208018396827573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1025672358442764783080389 192313567208018396827573)
                    ·
                      rfl

theorem cell23_1123588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 3, 2, 4].length) (baseStart_1123588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1123588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1123588 prefixEnd_1123588 := by exact prefixLift 1123588
  have htrace : WordTrace (prefixWord ++ tailWord_1123588) baseStart_1123588 baseEnd_1123588 := by
    simpa [prefixWord, tailWord_1123588, baseEnd_1123588] using wordTrace_append hprefix tailTrace_1123588
  have hstable : (prefixWord ++ tailWord_1123588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123588).length < 2 ^ (prefixWord ++ tailWord_1123588).sum := by decide
  have hdescent : baseEnd_1123588 < baseStart_1123588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123611 : List Nat := [1, 1, 1, 1, 1, 1, 5, 4, 4, 1, 3]
def baseStart_1123611 : Nat := 118140960795 + 1123611 * 2 ^ 59
def prefixEnd_1123611 : Nat := 4983230072969 + 3 ^ 40 * 1123611 * 2
def baseEnd_1123611 : Nat := 576952511679108600495113

theorem tailTrace_1123611 : CollatzResearch.WordTrace tailWord_1123611 prefixEnd_1123611 576952511679108600495113 := by
  unfold tailWord_1123611
  simp only [CollatzResearch.WordTrace]
  refine ⟨40981459932356719326170687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27320973288237812884113791 40981459932356719326170687)
  ·
    refine ⟨61472189898535078989256031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40981459932356719326170687 61472189898535078989256031)
    ·
      refine ⟨92208284847802618483884047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61472189898535078989256031 92208284847802618483884047)
      ·
        refine ⟨138312427271703927725826071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92208284847802618483884047 138312427271703927725826071)
        ·
          refine ⟨207468640907555891588739107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138312427271703927725826071 207468640907555891588739107)
          ·
            refine ⟨311202961361333837383108661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207468640907555891588739107 311202961361333837383108661)
            ·
              refine ⟨29175277627625047254666437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 311202961361333837383108661 29175277627625047254666437)
              ·
                refine ⟨5470364555179696360249957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29175277627625047254666437 5470364555179696360249957)
                ·
                  refine ⟨1025693354096193067546867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5470364555179696360249957 1025693354096193067546867)
                  ·
                    refine ⟨1538540031144289601320301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1025693354096193067546867 1538540031144289601320301)
                    ·
                      refine ⟨576952511679108600495113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1538540031144289601320301 576952511679108600495113)
                      ·
                        rfl

theorem cell23_1123611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 4, 1, 3].length) (baseStart_1123611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1123611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1123611 prefixEnd_1123611 := by exact prefixLift 1123611
  have htrace : WordTrace (prefixWord ++ tailWord_1123611) baseStart_1123611 baseEnd_1123611 := by
    simpa [prefixWord, tailWord_1123611, baseEnd_1123611] using wordTrace_append hprefix tailTrace_1123611
  have hstable : (prefixWord ++ tailWord_1123611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123611).length < 2 ^ (prefixWord ++ tailWord_1123611).sum := by decide
  have hdescent : baseEnd_1123611 < baseStart_1123611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123629 : List Nat := [1, 5, 3, 1, 1, 1, 2, 4, 1, 2, 2]
def baseStart_1123629 : Nat := 118140960795 + 1123629 * 2 ^ 59
def prefixEnd_1123629 : Nat := 4983230072969 + 3 ^ 40 * 1123629 * 2
def baseEnd_1123629 : Nat := 576961754330889530070031

theorem tailTrace_1123629 : CollatzResearch.WordTrace tailWord_1123629 prefixEnd_1123629 576961754330889530070031 := by
  unfold tailWord_1123629
  simp only [CollatzResearch.WordTrace]
  refine ⟨40982116446291508400325941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27321410964194338933550627 40982116446291508400325941)
  ·
    refine ⟨3842073416839828912530557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40982116446291508400325941 3842073416839828912530557)
    ·
      refine ⟨1440777531314935842198959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3842073416839828912530557 1440777531314935842198959)
      ·
        refine ⟨2161166296972403763298439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1440777531314935842198959 2161166296972403763298439)
        ·
          refine ⟨3241749445458605644947659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2161166296972403763298439 3241749445458605644947659)
          ·
            refine ⟨4862624168187908467421489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3241749445458605644947659 4862624168187908467421489)
            ·
              refine ⟨3646968126140931350566117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4862624168187908467421489 3646968126140931350566117)
              ·
                refine ⟨683806523651424628231147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3646968126140931350566117 683806523651424628231147)
                ·
                  refine ⟨1025709785477136942346721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 683806523651424628231147 1025709785477136942346721)
                  ·
                    refine ⟨769282339107852706760041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1025709785477136942346721 769282339107852706760041)
                    ·
                      refine ⟨576961754330889530070031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 769282339107852706760041 576961754330889530070031)
                      ·
                        rfl

theorem cell23_1123629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_1123629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1123629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1123629 prefixEnd_1123629 := by exact prefixLift 1123629
  have htrace : WordTrace (prefixWord ++ tailWord_1123629) baseStart_1123629 baseEnd_1123629 := by
    simpa [prefixWord, tailWord_1123629, baseEnd_1123629] using wordTrace_append hprefix tailTrace_1123629
  have hstable : (prefixWord ++ tailWord_1123629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123629).length < 2 ^ (prefixWord ++ tailWord_1123629).sum := by decide
  have hdescent : baseEnd_1123629 < baseStart_1123629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123655 : List Nat := [1, 1, 4, 1, 2, 4, 2, 2, 1, 3, 2]
def baseStart_1123655 : Nat := 118140960795 + 1123655 * 2 ^ 59
def prefixEnd_1123655 : Nat := 4983230072969 + 3 ^ 40 * 1123655 * 2
def baseEnd_1123655 : Nat := 576975104827906428344911

theorem tailTrace_1123655 : CollatzResearch.WordTrace tailWord_1123655 prefixEnd_1123655 576975104827906428344911 := by
  unfold tailWord_1123655
  simp only [CollatzResearch.WordTrace]
  refine ⟨40983064744197314840772419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27322043162798209893848279 40983064744197314840772419)
  ·
    refine ⟨61474597116295972261158629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40983064744197314840772419 61474597116295972261158629)
    ·
      refine ⟨11526486959305494798967243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61474597116295972261158629 11526486959305494798967243)
      ·
        refine ⟨17289730438958242198450865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11526486959305494798967243 17289730438958242198450865)
        ·
          refine ⟨12967297829218681648838149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17289730438958242198450865 12967297829218681648838149)
          ·
            refine ⟨2431368342978502809157153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12967297829218681648838149 2431368342978502809157153)
            ·
              refine ⟨1823526257233877106867865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2431368342978502809157153 1823526257233877106867865)
              ·
                refine ⟨1367644692925407830150899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1823526257233877106867865 1367644692925407830150899)
                ·
                  refine ⟨2051467039388111745226349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1367644692925407830150899 2051467039388111745226349)
                  ·
                    refine ⟨769300139770541904459881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2051467039388111745226349 769300139770541904459881)
                    ·
                      refine ⟨576975104827906428344911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 769300139770541904459881 576975104827906428344911)
                      ·
                        rfl

theorem cell23_1123655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 2, 1, 3, 2].length) (baseStart_1123655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1123655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1123655 prefixEnd_1123655 := by exact prefixLift 1123655
  have htrace : WordTrace (prefixWord ++ tailWord_1123655) baseStart_1123655 baseEnd_1123655 := by
    simpa [prefixWord, tailWord_1123655, baseEnd_1123655] using wordTrace_append hprefix tailTrace_1123655
  have hstable : (prefixWord ++ tailWord_1123655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123655).length < 2 ^ (prefixWord ++ tailWord_1123655).sum := by decide
  have hdescent : baseEnd_1123655 < baseStart_1123655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123668 : List Nat := [2, 4, 1, 1, 2, 1, 2, 1, 3, 4, 2]
def baseStart_1123668 : Nat := 118140960795 + 1123668 * 2 ^ 59
def prefixEnd_1123668 : Nat := 4983230072969 + 3 ^ 40 * 1123668 * 2
def baseEnd_1123668 : Nat := 576981780076414877482351

theorem tailTrace_1123668 : CollatzResearch.WordTrace tailWord_1123668 prefixEnd_1123668 576981780076414877482351 := by
  unfold tailWord_1123668
  simp only [CollatzResearch.WordTrace]
  refine ⟨20491769446575109030497829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27322359262100145373997105 20491769446575109030497829)
  ·
    refine ⟨3842206771232832943218343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20491769446575109030497829 3842206771232832943218343)
    ·
      refine ⟨5763310156849249414827515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3842206771232832943218343 5763310156849249414827515)
      ·
        refine ⟨8644965235273874122241273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5763310156849249414827515 8644965235273874122241273)
        ·
          refine ⟨6483723926455405591680955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8644965235273874122241273 6483723926455405591680955)
          ·
            refine ⟨9725585889683108387521433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6483723926455405591680955 9725585889683108387521433)
            ·
              refine ⟨7294189417262331290641075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9725585889683108387521433 7294189417262331290641075)
              ·
                refine ⟨10941284125893496935961613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7294189417262331290641075 10941284125893496935961613)
                ·
                  refine ⟨4102981547210061350985605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10941284125893496935961613 4102981547210061350985605)
                  ·
                    refine ⟨769309040101886503309801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4102981547210061350985605 769309040101886503309801)
                    ·
                      refine ⟨576981780076414877482351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 769309040101886503309801 576981780076414877482351)
                      ·
                        rfl

theorem cell23_1123668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 3, 4, 2].length) (baseStart_1123668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1123668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1123668 prefixEnd_1123668 := by exact prefixLift 1123668
  have htrace : WordTrace (prefixWord ++ tailWord_1123668) baseStart_1123668 baseEnd_1123668 := by
    simpa [prefixWord, tailWord_1123668, baseEnd_1123668] using wordTrace_append hprefix tailTrace_1123668
  have hstable : (prefixWord ++ tailWord_1123668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123668).length < 2 ^ (prefixWord ++ tailWord_1123668).sum := by decide
  have hdescent : baseEnd_1123668 < baseStart_1123668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123671 : List Nat := [1, 1, 3, 2, 3, 3, 1, 1, 2, 1, 5]
def baseStart_1123671 : Nat := 118140960795 + 1123671 * 2 ^ 59
def prefixEnd_1123671 : Nat := 4983230072969 + 3 ^ 40 * 1123671 * 2
def baseEnd_1123671 : Nat := 576983320518378365744837

theorem tailTrace_1123671 : CollatzResearch.WordTrace tailWord_1123671 prefixEnd_1123671 576983320518378365744837 := by
  unfold tailWord_1123671
  simp only [CollatzResearch.WordTrace]
  refine ⟨40983648312139349573354867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27322432208092899715569911 40983648312139349573354867)
  ·
    refine ⟨61475472468209024360032301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40983648312139349573354867 61475472468209024360032301)
    ·
      refine ⟨23053302175578384135012113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61475472468209024360032301 23053302175578384135012113)
      ·
        refine ⟨17289976631683788101259085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23053302175578384135012113 17289976631683788101259085)
        ·
          refine ⟨6483741236881420537972157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17289976631683788101259085 6483741236881420537972157)
          ·
            refine ⟨2431402963830532701739559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6483741236881420537972157 2431402963830532701739559)
            ·
              refine ⟨3647104445745799052609339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2431402963830532701739559 3647104445745799052609339)
              ·
                refine ⟨5470656668618698578914009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3647104445745799052609339 5470656668618698578914009)
                ·
                  refine ⟨4102992501464023934185507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5470656668618698578914009 4102992501464023934185507)
                  ·
                    refine ⟨6154488752196035901278261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4102992501464023934185507 6154488752196035901278261)
                    ·
                      refine ⟨576983320518378365744837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6154488752196035901278261 576983320518378365744837)
                      ·
                        rfl

theorem cell23_1123671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 2, 1, 5].length) (baseStart_1123671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1123671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1123671 prefixEnd_1123671 := by exact prefixLift 1123671
  have htrace : WordTrace (prefixWord ++ tailWord_1123671) baseStart_1123671 baseEnd_1123671 := by
    simpa [prefixWord, tailWord_1123671, baseEnd_1123671] using wordTrace_append hprefix tailTrace_1123671
  have hstable : (prefixWord ++ tailWord_1123671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123671).length < 2 ^ (prefixWord ++ tailWord_1123671).sum := by decide
  have hdescent : baseEnd_1123671 < baseStart_1123671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123674 : List Nat := [3, 1, 1, 2, 1, 2, 2, 2, 9]
def baseStart_1123674 : Nat := 118140960795 + 1123674 * 2 ^ 59
def prefixEnd_1123674 : Nat := 4983230072969 + 3 ^ 40 * 1123674 * 2
def baseEnd_1123674 : Nat := 64109428995593539334147

theorem tailTrace_1123674 : CollatzResearch.WordTrace tailWord_1123674 prefixEnd_1123674 64109428995593539334147 := by
  unfold tailWord_1123674
  simp only [CollatzResearch.WordTrace]
  refine ⟨10245939432782120271428519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27322505154085654057142717 10245939432782120271428519)
  ·
    refine ⟨15368909149173180407142779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10245939432782120271428519 15368909149173180407142779)
    ·
      refine ⟨23053363723759770610714169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15368909149173180407142779 23053363723759770610714169)
      ·
        refine ⟨17290022792819827958035627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23053363723759770610714169 17290022792819827958035627)
        ·
          refine ⟨25935034189229741937053441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17290022792819827958035627 25935034189229741937053441)
          ·
            refine ⟨19451275641922306452790081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25935034189229741937053441 19451275641922306452790081)
            ·
              refine ⟨14588456731441729839592561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19451275641922306452790081 14588456731441729839592561)
              ·
                refine ⟨10941342548581297379694421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14588456731441729839592561 10941342548581297379694421)
                ·
                  refine ⟨64109428995593539334147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 10941342548581297379694421 64109428995593539334147)
                  ·
                    rfl

theorem cell23_1123674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 9].length) (baseStart_1123674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1123674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1123674 prefixEnd_1123674 := by exact prefixLift 1123674
  have htrace : WordTrace (prefixWord ++ tailWord_1123674) baseStart_1123674 baseEnd_1123674 := by
    simpa [prefixWord, tailWord_1123674, baseEnd_1123674] using wordTrace_append hprefix tailTrace_1123674
  have hstable : (prefixWord ++ tailWord_1123674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123674).length < 2 ^ (prefixWord ++ tailWord_1123674).sum := by decide
  have hdescent : baseEnd_1123674 < baseStart_1123674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123685 : List Nat := [1, 3, 1, 3, 1, 2, 2, 4, 2, 2, 2]
def baseStart_1123685 : Nat := 118140960795 + 1123685 * 2 ^ 59
def prefixEnd_1123685 : Nat := 4983230072969 + 3 ^ 40 * 1123685 * 2
def baseEnd_1123685 : Nat := 576990509247541310969773

theorem tailTrace_1123685 : CollatzResearch.WordTrace tailWord_1123685 prefixEnd_1123685 576990509247541310969773 := by
  unfold tailWord_1123685
  simp only [CollatzResearch.WordTrace]
  refine ⟨40984158934088629964364509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27322772622725753309576339 40984158934088629964364509)
  ·
    refine ⟨15369059600283236236636691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40984158934088629964364509 15369059600283236236636691)
    ·
      refine ⟨23053589400424854354955037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15369059600283236236636691 23053589400424854354955037)
      ·
        refine ⟨8645096025159320383108139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23053589400424854354955037 8645096025159320383108139)
        ·
          refine ⟨12967644037738980574662209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8645096025159320383108139 12967644037738980574662209)
          ·
            refine ⟨9725733028304235430996657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12967644037738980574662209 9725733028304235430996657)
            ·
              refine ⟨7294299771228176573247493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9725733028304235430996657 7294299771228176573247493)
              ·
                refine ⟨1367681207105283107483905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7294299771228176573247493 1367681207105283107483905)
                ·
                  refine ⟨1025760905328962330612929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1367681207105283107483905 1025760905328962330612929)
                  ·
                    refine ⟨769320678996721747959697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1025760905328962330612929 769320678996721747959697)
                    ·
                      refine ⟨576990509247541310969773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 769320678996721747959697 576990509247541310969773)
                      ·
                        rfl

theorem cell23_1123685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 4, 2, 2, 2].length) (baseStart_1123685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1123685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1123685 prefixEnd_1123685 := by exact prefixLift 1123685
  have htrace : WordTrace (prefixWord ++ tailWord_1123685) baseStart_1123685 baseEnd_1123685 := by
    simpa [prefixWord, tailWord_1123685, baseEnd_1123685] using wordTrace_append hprefix tailTrace_1123685
  have hstable : (prefixWord ++ tailWord_1123685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123685).length < 2 ^ (prefixWord ++ tailWord_1123685).sum := by decide
  have hdescent : baseEnd_1123685 < baseStart_1123685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123742 : List Nat := [4, 3, 1, 2, 2, 1, 1, 4, 5]
def baseStart_1123742 : Nat := 118140960795 + 1123742 * 2 ^ 59
def prefixEnd_1123742 : Nat := 4983230072969 + 3 ^ 40 * 1123742 * 2
def baseEnd_1123742 : Nat := 64113308627205287550779

theorem tailTrace_1123742 : CollatzResearch.WordTrace tailWord_1123742 prefixEnd_1123742 64113308627205287550779 := by
  unfold tailWord_1123742
  simp only [CollatzResearch.WordTrace]
  refine ⟨5123279736860266087398685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27324158596588085799459653 5123279736860266087398685)
  ·
    refine ⟨1921229901322599782774507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5123279736860266087398685 1921229901322599782774507)
    ·
      refine ⟨2881844851983899674161761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1921229901322599782774507 2881844851983899674161761)
      ·
        refine ⟨2161383638987924755621321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2881844851983899674161761 2161383638987924755621321)
        ·
          refine ⟨1621037729240943566715991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2161383638987924755621321 1621037729240943566715991)
          ·
            refine ⟨2431556593861415350073987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1621037729240943566715991 2431556593861415350073987)
            ·
              refine ⟨3647334890792123025110981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2431556593861415350073987 3647334890792123025110981)
              ·
                refine ⟨683875292023523067208309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3647334890792123025110981 683875292023523067208309)
                ·
                  refine ⟨64113308627205287550779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 683875292023523067208309 64113308627205287550779)
                  ·
                    rfl

theorem cell23_1123742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_1123742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1123742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1123742 prefixEnd_1123742 := by exact prefixLift 1123742
  have htrace : WordTrace (prefixWord ++ tailWord_1123742) baseStart_1123742 baseEnd_1123742 := by
    simpa [prefixWord, tailWord_1123742, baseEnd_1123742] using wordTrace_append hprefix tailTrace_1123742
  have hstable : (prefixWord ++ tailWord_1123742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123742).length < 2 ^ (prefixWord ++ tailWord_1123742).sum := by decide
  have hdescent : baseEnd_1123742 < baseStart_1123742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123772 : List Nat := [2, 2, 2, 4, 3, 1, 1, 1, 2, 5]
def baseStart_1123772 : Nat := 118140960795 + 1123772 * 2 ^ 59
def prefixEnd_1123772 : Nat := 4983230072969 + 3 ^ 40 * 1123772 * 2
def baseEnd_1123772 : Nat := 192345060688160823527291

theorem tailTrace_1123772 : CollatzResearch.WordTrace tailWord_1123772 prefixEnd_1123772 192345060688160823527291 := by
  unfold tailWord_1123772
  simp only [CollatzResearch.WordTrace]
  refine ⟨20493666042386721911390785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27324888056515629215187713 20493666042386721911390785)
  ·
    refine ⟨15370249531790041433543089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20493666042386721911390785 15370249531790041433543089)
    ·
      refine ⟨11527687148842531075157317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15370249531790041433543089 11527687148842531075157317)
      ·
        refine ⟨2161441340407974576591997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11527687148842531075157317 2161441340407974576591997)
        ·
          refine ⟨810540502652990466221999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2161441340407974576591997 810540502652990466221999)
          ·
            refine ⟨1215810753979485699332999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 810540502652990466221999 1215810753979485699332999)
            ·
              refine ⟨1823716130969228548999499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1215810753979485699332999 1823716130969228548999499)
              ·
                refine ⟨2735574196453842823499249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1823716130969228548999499 2735574196453842823499249)
                ·
                  refine ⟨2051680647340382117624437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2735574196453842823499249 2051680647340382117624437)
                  ·
                    refine ⟨192345060688160823527291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2051680647340382117624437 192345060688160823527291)
                    ·
                      rfl

theorem cell23_1123772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 1, 2, 5].length) (baseStart_1123772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1123772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1123772 prefixEnd_1123772 := by exact prefixLift 1123772
  have htrace : WordTrace (prefixWord ++ tailWord_1123772) baseStart_1123772 baseEnd_1123772 := by
    simpa [prefixWord, tailWord_1123772, baseEnd_1123772] using wordTrace_append hprefix tailTrace_1123772
  have hstable : (prefixWord ++ tailWord_1123772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123772).length < 2 ^ (prefixWord ++ tailWord_1123772).sum := by decide
  have hdescent : baseEnd_1123772 < baseStart_1123772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123801 : List Nat := [1, 2, 1, 2, 4, 2, 1, 1, 1, 2, 6]
def baseStart_1123801 : Nat := 118140960795 + 1123801 * 2 ^ 59
def prefixEnd_1123801 : Nat := 4983230072969 + 3 ^ 40 * 1123801 * 2
def baseEnd_1123801 : Nat := 577050073003462857119239

theorem tailTrace_1123801 : CollatzResearch.WordTrace tailWord_1123801 prefixEnd_1123801 577050073003462857119239 := by
  unfold tailWord_1123801
  simp only [CollatzResearch.WordTrace]
  refine ⟨40988389801668381775587257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27325593201112254517058171 40988389801668381775587257)
  ·
    refine ⟨30741292351251286331690443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40988389801668381775587257 30741292351251286331690443)
    ·
      refine ⟨46111938526876929497535665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30741292351251286331690443 46111938526876929497535665)
      ·
        refine ⟨34583953895157697123151749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46111938526876929497535665 34583953895157697123151749)
        ·
          refine ⟨6484491355342068210590953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34583953895157697123151749 6484491355342068210590953)
          ·
            refine ⟨4863368516506551157943215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6484491355342068210590953 4863368516506551157943215)
            ·
              refine ⟨7295052774759826736914823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4863368516506551157943215 7295052774759826736914823)
              ·
                refine ⟨10942579162139740105372235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7295052774759826736914823 10942579162139740105372235)
                ·
                  refine ⟨16413868743209610158058353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10942579162139740105372235 16413868743209610158058353)
                  ·
                    refine ⟨12310401557407207618543765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16413868743209610158058353 12310401557407207618543765)
                    ·
                      refine ⟨577050073003462857119239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12310401557407207618543765 577050073003462857119239)
                      ·
                        rfl

theorem cell23_1123801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 2, 6].length) (baseStart_1123801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1123801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1123801 prefixEnd_1123801 := by exact prefixLift 1123801
  have htrace : WordTrace (prefixWord ++ tailWord_1123801) baseStart_1123801 baseEnd_1123801 := by
    simpa [prefixWord, tailWord_1123801, baseEnd_1123801] using wordTrace_append hprefix tailTrace_1123801
  have hstable : (prefixWord ++ tailWord_1123801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123801).length < 2 ^ (prefixWord ++ tailWord_1123801).sum := by decide
  have hdescent : baseEnd_1123801 < baseStart_1123801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123815 : List Nat := [1, 1, 5, 2, 1, 3, 3, 1, 6]
def baseStart_1123815 : Nat := 118140960795 + 1123815 * 2 ^ 59
def prefixEnd_1123815 : Nat := 4983230072969 + 3 ^ 40 * 1123815 * 2
def baseEnd_1123815 : Nat := 64117473525847311371575

theorem tailTrace_1123815 : CollatzResearch.WordTrace tailWord_1123815 prefixEnd_1123815 64117473525847311371575 := by
  unfold tailWord_1123815
  simp only [CollatzResearch.WordTrace]
  refine ⟨40988900423617662166596899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27325933615745108111064599 40988900423617662166596899)
  ·
    refine ⟨61483350635426493249895349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40988900423617662166596899 61483350635426493249895349)
    ·
      refine ⟨5764064122071233742177689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 61483350635426493249895349 5764064122071233742177689)
      ·
        refine ⟨4323048091553425306633267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5764064122071233742177689 4323048091553425306633267)
        ·
          refine ⟨6484572137330137959949901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4323048091553425306633267 6484572137330137959949901)
          ·
            refine ⟨2431714551498801734981213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6484572137330137959949901 2431714551498801734981213)
            ·
              refine ⟨911892956812050650617955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2431714551498801734981213 911892956812050650617955)
              ·
                refine ⟨1367839435218075975926933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 911892956812050650617955 1367839435218075975926933)
                ·
                  refine ⟨64117473525847311371575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1367839435218075975926933 64117473525847311371575)
                  ·
                    rfl

theorem cell23_1123815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 3, 1, 6].length) (baseStart_1123815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1123815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1123815 prefixEnd_1123815 := by exact prefixLift 1123815
  have htrace : WordTrace (prefixWord ++ tailWord_1123815) baseStart_1123815 baseEnd_1123815 := by
    simpa [prefixWord, tailWord_1123815, baseEnd_1123815] using wordTrace_append hprefix tailTrace_1123815
  have hstable : (prefixWord ++ tailWord_1123815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123815).length < 2 ^ (prefixWord ++ tailWord_1123815).sum := by decide
  have hdescent : baseEnd_1123815 < baseStart_1123815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123825 : List Nat := [1, 2, 2, 2, 3, 2, 2, 2, 3, 1, 3]
def baseStart_1123825 : Nat := 118140960795 + 1123825 * 2 ^ 59
def prefixEnd_1123825 : Nat := 4983230072969 + 3 ^ 40 * 1123825 * 2
def baseEnd_1123825 : Nat := 577062396539170763219129

theorem tailTrace_1123825 : CollatzResearch.WordTrace tailWord_1123825 prefixEnd_1123825 577062396539170763219129 := by
  unfold tailWord_1123825
  simp only [CollatzResearch.WordTrace]
  refine ⟨40989265153581433874460929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27326176769054289249640619 40989265153581433874460929)
  ·
    refine ⟨30741948865186075405845697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40989265153581433874460929 30741948865186075405845697)
    ·
      refine ⟨23056461648889556554384273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30741948865186075405845697 23056461648889556554384273)
      ·
        refine ⟨17292346236667167415788205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23056461648889556554384273 17292346236667167415788205)
        ·
          refine ⟨6484629838750187780920577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17292346236667167415788205 6484629838750187780920577)
          ·
            refine ⟨4863472379062640835690433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6484629838750187780920577 4863472379062640835690433)
            ·
              refine ⟨3647604284296980626767825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4863472379062640835690433 3647604284296980626767825)
              ·
                refine ⟨2735703213222735470075869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3647604284296980626767825 2735703213222735470075869)
                ·
                  refine ⟨1025888704958525801278451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2735703213222735470075869 1025888704958525801278451)
                  ·
                    refine ⟨1538833057437788701917677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1025888704958525801278451 1538833057437788701917677)
                    ·
                      refine ⟨577062396539170763219129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1538833057437788701917677 577062396539170763219129)
                      ·
                        rfl

theorem cell23_1123825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 2, 3, 1, 3].length) (baseStart_1123825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1123825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1123825 prefixEnd_1123825 := by exact prefixLift 1123825
  have htrace : WordTrace (prefixWord ++ tailWord_1123825) baseStart_1123825 baseEnd_1123825 := by
    simpa [prefixWord, tailWord_1123825, baseEnd_1123825] using wordTrace_append hprefix tailTrace_1123825
  have hstable : (prefixWord ++ tailWord_1123825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123825).length < 2 ^ (prefixWord ++ tailWord_1123825).sum := by decide
  have hdescent : baseEnd_1123825 < baseStart_1123825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123846 : List Nat := [6, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3]
def baseStart_1123846 : Nat := 118140960795 + 1123846 * 2 ^ 59
def prefixEnd_1123846 : Nat := 4983230072969 + 3 ^ 40 * 1123846 * 2
def baseEnd_1123846 : Nat := 577073179632915181056533

theorem tailTrace_1123846 : CollatzResearch.WordTrace tailWord_1123846 prefixEnd_1123846 577073179632915181056533 := by
  unfold tailWord_1123846
  simp only [CollatzResearch.WordTrace]
  refine ⟨1280938471453292326905481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 27326687391003569640650261 1280938471453292326905481)
  ·
    refine ⟨960703853589969245179111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1280938471453292326905481 960703853589969245179111)
    ·
      refine ⟨1441055780384953867768667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 960703853589969245179111 1441055780384953867768667)
      ·
        refine ⟨2161583670577430801653001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1441055780384953867768667 2161583670577430801653001)
        ·
          refine ⟨1621187752933073101239751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2161583670577430801653001 1621187752933073101239751)
          ·
            refine ⟨2431781629399609651859627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1621187752933073101239751 2431781629399609651859627)
            ·
              refine ⟨3647672444099414477789441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2431781629399609651859627 3647672444099414477789441)
              ·
                refine ⟨2735754333074560858342081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3647672444099414477789441 2735754333074560858342081)
                ·
                  refine ⟨2051815749805920643756561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2735754333074560858342081 2051815749805920643756561)
                  ·
                    refine ⟨1538861812354440482817421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2051815749805920643756561 1538861812354440482817421)
                    ·
                      refine ⟨577073179632915181056533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1538861812354440482817421 577073179632915181056533)
                      ·
                        rfl

theorem cell23_1123846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_1123846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1123846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1123846 prefixEnd_1123846 := by exact prefixLift 1123846
  have htrace : WordTrace (prefixWord ++ tailWord_1123846) baseStart_1123846 baseEnd_1123846 := by
    simpa [prefixWord, tailWord_1123846, baseEnd_1123846] using wordTrace_append hprefix tailTrace_1123846
  have hstable : (prefixWord ++ tailWord_1123846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123846).length < 2 ^ (prefixWord ++ tailWord_1123846).sum := by decide
  have hdescent : baseEnd_1123846 < baseStart_1123846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123852 : List Nat := [2, 2, 1, 2, 5, 1, 1, 2, 2, 3, 2]
def baseStart_1123852 : Nat := 118140960795 + 1123852 * 2 ^ 59
def prefixEnd_1123852 : Nat := 4983230072969 + 3 ^ 40 * 1123852 * 2
def baseEnd_1123852 : Nat := 577076260516842157581505

theorem tailTrace_1123852 : CollatzResearch.WordTrace tailWord_1123852 prefixEnd_1123852 577076260516842157581505 := by
  unfold tailWord_1123852
  simp only [CollatzResearch.WordTrace]
  refine ⟨20495124962241808742846905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27326833282989078323795873 20495124962241808742846905)
  ·
    refine ⟨15371343721681356557135179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20495124962241808742846905 15371343721681356557135179)
    ·
      refine ⟨23057015582522034835702769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15371343721681356557135179 23057015582522034835702769)
      ·
        refine ⟨17292761686891526126777077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23057015582522034835702769 17292761686891526126777077)
        ·
          refine ⟨1621196408146080574385351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17292761686891526126777077 1621196408146080574385351)
          ·
            refine ⟨2431794612219120861578027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1621196408146080574385351 2431794612219120861578027)
            ·
              refine ⟨3647691918328681292367041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2431794612219120861578027 3647691918328681292367041)
              ·
                refine ⟨2735768938746510969275281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3647691918328681292367041 2735768938746510969275281)
                ·
                  refine ⟨2051826704059883226956461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2735768938746510969275281 2051826704059883226956461)
                  ·
                    refine ⟨769435014022456210108673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2051826704059883226956461 769435014022456210108673)
                    ·
                      refine ⟨577076260516842157581505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 769435014022456210108673 577076260516842157581505)
                      ·
                        rfl

theorem cell23_1123852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 2, 2, 3, 2].length) (baseStart_1123852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1123852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1123852 prefixEnd_1123852 := by exact prefixLift 1123852
  have htrace : WordTrace (prefixWord ++ tailWord_1123852) baseStart_1123852 baseEnd_1123852 := by
    simpa [prefixWord, tailWord_1123852, baseEnd_1123852] using wordTrace_append hprefix tailTrace_1123852
  have hstable : (prefixWord ++ tailWord_1123852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123852).length < 2 ^ (prefixWord ++ tailWord_1123852).sum := by decide
  have hdescent : baseEnd_1123852 < baseStart_1123852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123853 : List Nat := [1, 7, 1, 1, 2, 1, 3, 2, 1, 4]
def baseStart_1123853 : Nat := 118140960795 + 1123853 * 2 ^ 59
def prefixEnd_1123853 : Nat := 4983230072969 + 3 ^ 40 * 1123853 * 2
def baseEnd_1123853 : Nat := 192358924665832217889667

theorem tailTrace_1123853 : CollatzResearch.WordTrace tailWord_1123853 prefixEnd_1123853 192358924665832217889667 := by
  unfold tailWord_1123853
  simp only [CollatzResearch.WordTrace]
  refine ⟨40990286397479994656480213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27326857598319996437653475 40990286397479994656480213)
  ·
    refine ⟨960709837440937374761255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 40990286397479994656480213 960709837440937374761255)
    ·
      refine ⟨1441064756161406062141883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 960709837440937374761255 1441064756161406062141883)
      ·
        refine ⟨2161597134242109093212825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1441064756161406062141883 2161597134242109093212825)
        ·
          refine ⟨1621197850681581819909619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2161597134242109093212825 1621197850681581819909619)
          ·
            refine ⟨2431796776022372729864429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1621197850681581819909619 2431796776022372729864429)
            ·
              refine ⟨911923791008389773699161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2431796776022372729864429 911923791008389773699161)
              ·
                refine ⟨683942843256292330274371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 911923791008389773699161 683942843256292330274371)
                ·
                  refine ⟨1025914264884438495411557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 683942843256292330274371 1025914264884438495411557)
                  ·
                    refine ⟨192358924665832217889667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1025914264884438495411557 192358924665832217889667)
                    ·
                      rfl

theorem cell23_1123853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_1123853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1123853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1123853 prefixEnd_1123853 := by exact prefixLift 1123853
  have htrace : WordTrace (prefixWord ++ tailWord_1123853) baseStart_1123853 baseEnd_1123853 := by
    simpa [prefixWord, tailWord_1123853, baseEnd_1123853] using wordTrace_append hprefix tailTrace_1123853
  have hstable : (prefixWord ++ tailWord_1123853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123853).length < 2 ^ (prefixWord ++ tailWord_1123853).sum := by decide
  have hdescent : baseEnd_1123853 < baseStart_1123853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123859 : List Nat := [1, 1, 1, 2, 1, 7, 3, 2, 1, 1, 3]
def baseStart_1123859 : Nat := 118140960795 + 1123859 * 2 ^ 59
def prefixEnd_1123859 : Nat := 4983230072969 + 3 ^ 40 * 1123859 * 2
def baseEnd_1123859 : Nat := 577079854881423630193973

theorem tailTrace_1123859 : CollatzResearch.WordTrace tailWord_1123859 prefixEnd_1123859 577079854881423630193973 := by
  unfold tailWord_1123859
  simp only [CollatzResearch.WordTrace]
  refine ⟨40990505235458257681198631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27327003490305505120799087 40990505235458257681198631)
  ·
    refine ⟨61485757853187386521797947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40990505235458257681198631 61485757853187386521797947)
    ·
      refine ⟨92228636779781079782696921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61485757853187386521797947 92228636779781079782696921)
      ·
        refine ⟨69171477584835809837022691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92228636779781079782696921 69171477584835809837022691)
        ·
          refine ⟨103757216377253714755534037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69171477584835809837022691 103757216377253714755534037)
          ·
            refine ⟨2431809758841883939582829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 103757216377253714755534037 2431809758841883939582829)
            ·
              refine ⟨911928659565706477343561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2431809758841883939582829 911928659565706477343561)
              ·
                refine ⟨683946494674279858007671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 911928659565706477343561 683946494674279858007671)
                ·
                  refine ⟨1025919742011419787011507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 683946494674279858007671 1025919742011419787011507)
                  ·
                    refine ⟨1538879613017129680517261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1025919742011419787011507 1538879613017129680517261)
                    ·
                      refine ⟨577079854881423630193973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1538879613017129680517261 577079854881423630193973)
                      ·
                        rfl

theorem cell23_1123859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 3, 2, 1, 1, 3].length) (baseStart_1123859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1123859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1123859 prefixEnd_1123859 := by exact prefixLift 1123859
  have htrace : WordTrace (prefixWord ++ tailWord_1123859) baseStart_1123859 baseEnd_1123859 := by
    simpa [prefixWord, tailWord_1123859, baseEnd_1123859] using wordTrace_append hprefix tailTrace_1123859
  have hstable : (prefixWord ++ tailWord_1123859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123859).length < 2 ^ (prefixWord ++ tailWord_1123859).sum := by decide
  have hdescent : baseEnd_1123859 < baseStart_1123859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123868 : List Nat := [2, 2, 3, 1, 2, 1, 1, 4, 1, 1, 5]
def baseStart_1123868 : Nat := 118140960795 + 1123868 * 2 ^ 59
def prefixEnd_1123868 : Nat := 4983230072969 + 3 ^ 40 * 1123868 * 2
def baseEnd_1123868 : Nat := 577084476207314094981431

theorem tailTrace_1123868 : CollatzResearch.WordTrace tailWord_1123868 prefixEnd_1123868 577084476207314094981431 := by
  unfold tailWord_1123868
  simp only [CollatzResearch.WordTrace]
  refine ⟨20495416746212826109138129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27327222328283768145517505 20495416746212826109138129)
  ·
    refine ⟨15371562559659619581853597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20495416746212826109138129 15371562559659619581853597)
    ·
      refine ⟨5764335959872357343195099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15371562559659619581853597 5764335959872357343195099)
      ·
        refine ⟨8646503939808536014792649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5764335959872357343195099 8646503939808536014792649)
        ·
          refine ⟨6484877954856402011094487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8646503939808536014792649 6484877954856402011094487)
          ·
            refine ⟨9727316932284603016641731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6484877954856402011094487 9727316932284603016641731)
            ·
              refine ⟨14590975398426904524962597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9727316932284603016641731 14590975398426904524962597)
              ·
                refine ⟨2735807887205044598430487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14590975398426904524962597 2735807887205044598430487)
                ·
                  refine ⟨4103711830807566897645731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2735807887205044598430487 4103711830807566897645731)
                  ·
                    refine ⟨6155567746211350346468597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4103711830807566897645731 6155567746211350346468597)
                    ·
                      refine ⟨577084476207314094981431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6155567746211350346468597 577084476207314094981431)
                      ·
                        rfl

theorem cell23_1123868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_1123868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1123868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1123868 prefixEnd_1123868 := by exact prefixLift 1123868
  have htrace : WordTrace (prefixWord ++ tailWord_1123868) baseStart_1123868 baseEnd_1123868 := by
    simpa [prefixWord, tailWord_1123868, baseEnd_1123868] using wordTrace_append hprefix tailTrace_1123868
  have hstable : (prefixWord ++ tailWord_1123868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123868).length < 2 ^ (prefixWord ++ tailWord_1123868).sum := by decide
  have hdescent : baseEnd_1123868 < baseStart_1123868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123871 : List Nat := [1, 1, 2, 4, 1, 1, 3, 10]
def baseStart_1123871 : Nat := 118140960795 + 1123871 * 2 ^ 59
def prefixEnd_1123871 : Nat := 4983230072969 + 3 ^ 40 * 1123871 * 2
def baseEnd_1123871 : Nat := 21373556172195466046071

theorem tailTrace_1123871 : CollatzResearch.WordTrace tailWord_1123871 prefixEnd_1123871 21373556172195466046071 := by
  unfold tailWord_1123871
  simp only [CollatzResearch.WordTrace]
  refine ⟨40990942911414783730635467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27327295274276522487090311 40990942911414783730635467)
  ·
    refine ⟨61486414367122175595953201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40990942911414783730635467 61486414367122175595953201)
    ·
      refine ⟨46114810775341631696964901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61486414367122175595953201 46114810775341631696964901)
      ·
        refine ⟨8646527020376555943180919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46114810775341631696964901 8646527020376555943180919)
        ·
          refine ⟨12969790530564833914771379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8646527020376555943180919 12969790530564833914771379)
          ·
            refine ⟨19454685795847250872157069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12969790530564833914771379 19454685795847250872157069)
            ·
              refine ⟨7295507173442719077058901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19454685795847250872157069 7295507173442719077058901)
              ·
                refine ⟨21373556172195466046071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 7295507173442719077058901 21373556172195466046071)
                ·
                  rfl

theorem cell23_1123871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 10].length) (baseStart_1123871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1123871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1123871 prefixEnd_1123871 := by exact prefixLift 1123871
  have htrace : WordTrace (prefixWord ++ tailWord_1123871) baseStart_1123871 baseEnd_1123871 := by
    simpa [prefixWord, tailWord_1123871, baseEnd_1123871] using wordTrace_append hprefix tailTrace_1123871
  have hstable : (prefixWord ++ tailWord_1123871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123871).length < 2 ^ (prefixWord ++ tailWord_1123871).sum := by decide
  have hdescent : baseEnd_1123871 < baseStart_1123871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123882 : List Nat := [3, 1, 4, 1, 1, 1, 2, 1, 5, 2, 2]
def baseStart_1123882 : Nat := 118140960795 + 1123882 * 2 ^ 59
def prefixEnd_1123882 : Nat := 4983230072969 + 3 ^ 40 * 1123882 * 2
def baseEnd_1123882 : Nat := 577091664936477040206367

theorem tailTrace_1123882 : CollatzResearch.WordTrace tailWord_1123882 prefixEnd_1123882 577091664936477040206367 := by
  unfold tailWord_1123882
  simp only [CollatzResearch.WordTrace]
  refine ⟨10247836028593733152321475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27327562742916621739523933 10247836028593733152321475)
  ·
    refine ⟨15371754042890599728482213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10247836028593733152321475 15371754042890599728482213)
    ·
      refine ⟨2882203883041987449090415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15371754042890599728482213 2882203883041987449090415)
      ·
        refine ⟨4323305824562981173635623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2882203883041987449090415 4323305824562981173635623)
        ·
          refine ⟨6484958736844471760453435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4323305824562981173635623 6484958736844471760453435)
          ·
            refine ⟨9727438105266707640680153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6484958736844471760453435 9727438105266707640680153)
            ·
              refine ⟨7295578578950030730510115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9727438105266707640680153 7295578578950030730510115)
              ·
                refine ⟨10943367868425046095765173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7295578578950030730510115 10943367868425046095765173)
                ·
                  refine ⟨1025940737664848071477985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10943367868425046095765173 1025940737664848071477985)
                  ·
                    refine ⟨769455553248636053608489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1025940737664848071477985 769455553248636053608489)
                    ·
                      refine ⟨577091664936477040206367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 769455553248636053608489 577091664936477040206367)
                      ·
                        rfl

theorem cell23_1123882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 5, 2, 2].length) (baseStart_1123882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1123882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1123882 prefixEnd_1123882 := by exact prefixLift 1123882
  have htrace : WordTrace (prefixWord ++ tailWord_1123882) baseStart_1123882 baseEnd_1123882 := by
    simpa [prefixWord, tailWord_1123882, baseEnd_1123882] using wordTrace_append hprefix tailTrace_1123882
  have hstable : (prefixWord ++ tailWord_1123882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123882).length < 2 ^ (prefixWord ++ tailWord_1123882).sum := by decide
  have hdescent : baseEnd_1123882 < baseStart_1123882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123910 : List Nat := [6, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3]
def baseStart_1123910 : Nat := 118140960795 + 1123910 * 2 ^ 59
def prefixEnd_1123910 : Nat := 4983230072969 + 3 ^ 40 * 1123910 * 2
def baseEnd_1123910 : Nat := 577106042394802930656239

theorem tailTrace_1123910 : CollatzResearch.WordTrace tailWord_1123910 prefixEnd_1123910 577106042394802930656239 := by
  unfold tailWord_1123910
  simp only [CollatzResearch.WordTrace]
  refine ⟨1281011417446046668478287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 27328243572182328927536789 1281011417446046668478287)
  ·
    refine ⟨1921517126169070002717431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1281011417446046668478287 1921517126169070002717431)
    ·
      refine ⟨2882275689253605004076147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1921517126169070002717431 2882275689253605004076147)
      ·
        refine ⟨4323413533880407506114221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2882275689253605004076147 4323413533880407506114221)
        ·
          refine ⟨1621280075205152814792833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4323413533880407506114221 1621280075205152814792833)
          ·
            refine ⟨1215960056403864611094625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1621280075205152814792833 1215960056403864611094625)
            ·
              refine ⟨911970042302898458320969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1215960056403864611094625 911970042302898458320969)
              ·
                refine ⟨683977531727173843740727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 911970042302898458320969 683977531727173843740727)
                ·
                  refine ⟨1025966297590760765611091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 683977531727173843740727 1025966297590760765611091)
                  ·
                    refine ⟨1538949446386141148416637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1025966297590760765611091 1538949446386141148416637)
                    ·
                      refine ⟨577106042394802930656239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1538949446386141148416637 577106042394802930656239)
                      ·
                        rfl

theorem cell23_1123910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3].length) (baseStart_1123910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1123910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1123910 prefixEnd_1123910 := by exact prefixLift 1123910
  have htrace : WordTrace (prefixWord ++ tailWord_1123910) baseStart_1123910 baseEnd_1123910 := by
    simpa [prefixWord, tailWord_1123910, baseEnd_1123910] using wordTrace_append hprefix tailTrace_1123910
  have hstable : (prefixWord ++ tailWord_1123910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123910).length < 2 ^ (prefixWord ++ tailWord_1123910).sum := by decide
  have hdescent : baseEnd_1123910 < baseStart_1123910 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123916 : List Nat := [2, 2, 1, 3, 1, 3, 4, 2, 1, 2, 2]
def baseStart_1123916 : Nat := 118140960795 + 1123916 * 2 ^ 59
def prefixEnd_1123916 : Nat := 4983230072969 + 3 ^ 40 * 1123916 * 2
def baseEnd_1123916 : Nat := 577109123278729907181211

theorem tailTrace_1123916 : CollatzResearch.WordTrace tailWord_1123916 prefixEnd_1123916 577109123278729907181211 := by
  unfold tailWord_1123916
  simp only [CollatzResearch.WordTrace]
  refine ⟨20496292098125878208011801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27328389464167837610682401 20496292098125878208011801)
  ·
    refine ⟨15372219073594408656008851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20496292098125878208011801 15372219073594408656008851)
    ·
      refine ⟨23058328610391612984013277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15372219073594408656008851 23058328610391612984013277)
      ·
        refine ⟨8646873228896854869004979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23058328610391612984013277 8646873228896854869004979)
        ·
          refine ⟨12970309843345282303507469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8646873228896854869004979 12970309843345282303507469)
          ·
            refine ⟨4863866191254480863815301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12970309843345282303507469 4863866191254480863815301)
            ·
              refine ⟨911974910860215161965369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4863866191254480863815301 911974910860215161965369)
              ·
                refine ⟨683981183145161371474027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 911974910860215161965369 683981183145161371474027)
                ·
                  refine ⟨1025971774717742057211041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 683981183145161371474027 1025971774717742057211041)
                  ·
                    refine ⟨769478831038306542908281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1025971774717742057211041 769478831038306542908281)
                    ·
                      refine ⟨577109123278729907181211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 769478831038306542908281 577109123278729907181211)
                      ·
                        rfl

theorem cell23_1123916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 4, 2, 1, 2, 2].length) (baseStart_1123916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1123916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1123916 prefixEnd_1123916 := by exact prefixLift 1123916
  have htrace : WordTrace (prefixWord ++ tailWord_1123916) baseStart_1123916 baseEnd_1123916 := by
    simpa [prefixWord, tailWord_1123916, baseEnd_1123916] using wordTrace_append hprefix tailTrace_1123916
  have hstable : (prefixWord ++ tailWord_1123916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123916).length < 2 ^ (prefixWord ++ tailWord_1123916).sum := by decide
  have hdescent : baseEnd_1123916 < baseStart_1123916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123932 : List Nat := [2, 2, 4, 1, 2, 2, 2, 1, 1, 3, 3]
def baseStart_1123932 : Nat := 118140960795 + 1123932 * 2 ^ 59
def prefixEnd_1123932 : Nat := 4983230072969 + 3 ^ 40 * 1123932 * 2
def baseEnd_1123932 : Nat := 577117338969201844581137

theorem tailTrace_1123932 : CollatzResearch.WordTrace tailWord_1123932 prefixEnd_1123932 577117338969201844581137 := by
  unfold tailWord_1123932
  simp only [CollatzResearch.WordTrace]
  refine ⟨20496583882096895574303025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27328778509462527432404033 20496583882096895574303025)
  ·
    refine ⟨15372437911572671680727269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20496583882096895574303025 15372437911572671680727269)
    ·
      refine ⟨2882332108419875940136363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15372437911572671680727269 2882332108419875940136363)
      ·
        refine ⟨4323498162629813910204545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2882332108419875940136363 4323498162629813910204545)
        ·
          refine ⟨3242623621972360432653409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4323498162629813910204545 3242623621972360432653409)
          ·
            refine ⟨2431967716479270324490057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3242623621972360432653409 2431967716479270324490057)
            ·
              refine ⟨1823975787359452743367543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2431967716479270324490057 1823975787359452743367543)
              ·
                refine ⟨2735963681039179115051315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1823975787359452743367543 2735963681039179115051315)
                ·
                  refine ⟨4103945521558768672576973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2735963681039179115051315 4103945521558768672576973)
                  ·
                    refine ⟨1538979570584538252216365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4103945521558768672576973 1538979570584538252216365)
                    ·
                      refine ⟨577117338969201844581137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1538979570584538252216365 577117338969201844581137)
                      ·
                        rfl

theorem cell23_1123932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_1123932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1123932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1123932 prefixEnd_1123932 := by exact prefixLift 1123932
  have htrace : WordTrace (prefixWord ++ tailWord_1123932) baseStart_1123932 baseEnd_1123932 := by
    simpa [prefixWord, tailWord_1123932, baseEnd_1123932] using wordTrace_append hprefix tailTrace_1123932
  have hstable : (prefixWord ++ tailWord_1123932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123932).length < 2 ^ (prefixWord ++ tailWord_1123932).sum := by decide
  have hdescent : baseEnd_1123932 < baseStart_1123932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123968 : List Nat := [2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 4]
def baseStart_1123968 : Nat := 118140960795 + 1123968 * 2 ^ 59
def prefixEnd_1123968 : Nat := 4983230072969 + 3 ^ 40 * 1123968 * 2
def baseEnd_1123968 : Nat := 577135824272763703730971

theorem tailTrace_1123968 : CollatzResearch.WordTrace tailWord_1123968 prefixEnd_1123968 577135824272763703730971 := by
  unfold tailWord_1123968
  simp only [CollatzResearch.WordTrace]
  refine ⟨20497240396031684648458279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27329653861375579531277705 20497240396031684648458279)
  ·
    refine ⟨30745860594047526972687419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20497240396031684648458279 30745860594047526972687419)
    ·
      refine ⟨46118790891071290459031129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30745860594047526972687419 46118790891071290459031129)
      ·
        refine ⟨34589093168303467844273347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46118790891071290459031129 34589093168303467844273347)
        ·
          refine ⟨51883639752455201766410021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34589093168303467844273347 51883639752455201766410021)
          ·
            refine ⟨9728182453585350331201879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51883639752455201766410021 9728182453585350331201879)
            ·
              refine ⟨14592273680378025496802819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9728182453585350331201879 14592273680378025496802819)
              ·
                refine ⟨21888410520567038245204229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14592273680378025496802819 21888410520567038245204229)
                ·
                  refine ⟨4104076972606319670975793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21888410520567038245204229 4104076972606319670975793)
                  ·
                    refine ⟨3078057729454739753231845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4104076972606319670975793 3078057729454739753231845)
                    ·
                      refine ⟨577135824272763703730971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3078057729454739753231845 577135824272763703730971)
                      ·
                        rfl

theorem cell23_1123968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 4].length) (baseStart_1123968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1123968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1123968 prefixEnd_1123968 := by exact prefixLift 1123968
  have htrace : WordTrace (prefixWord ++ tailWord_1123968) baseStart_1123968 baseEnd_1123968 := by
    simpa [prefixWord, tailWord_1123968, baseEnd_1123968] using wordTrace_append hprefix tailTrace_1123968
  have hstable : (prefixWord ++ tailWord_1123968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123968).length < 2 ^ (prefixWord ++ tailWord_1123968).sum := by decide
  have hdescent : baseEnd_1123968 < baseStart_1123968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124055 : List Nat := [1, 1, 3, 2, 1, 3, 2, 1, 5, 4]
def baseStart_1124055 : Nat := 118140960795 + 1124055 * 2 ^ 59
def prefixEnd_1124055 : Nat := 4983230072969 + 3 ^ 40 * 1124055 * 2
def baseEnd_1124055 : Nat := 192393499029901621114357

theorem tailTrace_1124055 : CollatzResearch.WordTrace tailWord_1124055 prefixEnd_1124055 192393499029901621114357 := by
  unfold tailWord_1124055
  simp only [CollatzResearch.WordTrace]
  refine ⟨40997653942748183155333619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27331769295165455436889079 40997653942748183155333619)
  ·
    refine ⟨61496480914122274733000429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40997653942748183155333619 61496480914122274733000429)
    ·
      refine ⟨23061180342795853024875161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61496480914122274733000429 23061180342795853024875161)
      ·
        refine ⟨17295885257096889768656371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23061180342795853024875161 17295885257096889768656371)
        ·
          refine ⟨25943827885645334652984557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17295885257096889768656371 25943827885645334652984557)
          ·
            refine ⟨9728935457117000494869209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25943827885645334652984557 9728935457117000494869209)
            ·
              refine ⟨7296701592837750371151907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9728935457117000494869209 7296701592837750371151907)
              ·
                refine ⟨10945052389256625556727861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7296701592837750371151907 10945052389256625556727861)
                ·
                  refine ⟨1026098661492808645943237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10945052389256625556727861 1026098661492808645943237)
                  ·
                    refine ⟨192393499029901621114357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1026098661492808645943237 192393499029901621114357)
                    ·
                      rfl

theorem cell23_1124055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 5, 4].length) (baseStart_1124055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1124055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1124055 prefixEnd_1124055 := by exact prefixLift 1124055
  have htrace : WordTrace (prefixWord ++ tailWord_1124055) baseStart_1124055 baseEnd_1124055 := by
    simpa [prefixWord, tailWord_1124055, baseEnd_1124055] using wordTrace_append hprefix tailTrace_1124055
  have hstable : (prefixWord ++ tailWord_1124055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124055).length < 2 ^ (prefixWord ++ tailWord_1124055).sum := by decide
  have hdescent : baseEnd_1124055 < baseStart_1124055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124082 : List Nat := [3, 2, 1, 3, 1, 1, 1, 4, 2, 2, 3]
def baseStart_1124082 : Nat := 118140960795 + 1124082 * 2 ^ 59
def prefixEnd_1124082 : Nat := 4983230072969 + 3 ^ 40 * 1124082 * 2
def baseEnd_1124082 : Nat := 577194361067376257705447

theorem tailTrace_1124082 : CollatzResearch.WordTrace tailWord_1124082 prefixEnd_1124082 577194361067376257705447 := by
  unfold tailWord_1124082
  simp only [CollatzResearch.WordTrace]
  refine ⟨10249659678412591691641625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27332425809100244511044333 10249659678412591691641625)
  ·
    refine ⟨7687244758809443768731219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10249659678412591691641625 7687244758809443768731219)
    ·
      refine ⟨11530867138214165653096829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7687244758809443768731219 11530867138214165653096829)
      ·
        refine ⟨4324075176830312119911311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11530867138214165653096829 4324075176830312119911311)
        ·
          refine ⟨6486112765245468179866967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4324075176830312119911311 6486112765245468179866967)
          ·
            refine ⟨9729169147868202269800451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6486112765245468179866967 9729169147868202269800451)
            ·
              refine ⟨14593753721802303404700677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9729169147868202269800451 14593753721802303404700677)
              ·
                refine ⟨2736328822837931888381377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14593753721802303404700677 2736328822837931888381377)
                ·
                  refine ⟨2052246617128448916286033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2736328822837931888381377 2052246617128448916286033)
                  ·
                    refine ⟨1539184962846336687214525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2052246617128448916286033 1539184962846336687214525)
                    ·
                      refine ⟨577194361067376257705447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1539184962846336687214525 577194361067376257705447)
                      ·
                        rfl

theorem cell23_1124082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_1124082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1124082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1124082 prefixEnd_1124082 := by exact prefixLift 1124082
  have htrace : WordTrace (prefixWord ++ tailWord_1124082) baseStart_1124082 baseEnd_1124082 := by
    simpa [prefixWord, tailWord_1124082, baseEnd_1124082] using wordTrace_append hprefix tailTrace_1124082
  have hstable : (prefixWord ++ tailWord_1124082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124082).length < 2 ^ (prefixWord ++ tailWord_1124082).sum := by decide
  have hdescent : baseEnd_1124082 < baseStart_1124082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124146 : List Nat := [3, 2, 1, 1, 3, 2, 2, 4, 1, 1, 3]
def baseStart_1124146 : Nat := 118140960795 + 1124146 * 2 ^ 59
def prefixEnd_1124146 : Nat := 4983230072969 + 3 ^ 40 * 1124146 * 2
def baseEnd_1124146 : Nat := 577227223829264007305153

theorem tailTrace_1124146 : CollatzResearch.WordTrace tailWord_1124146 prefixEnd_1124146 577227223829264007305153 := by
  unfold tailWord_1124146
  simp only [CollatzResearch.WordTrace]
  refine ⟨10250243246354626424224073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27333981990279003797930861 10250243246354626424224073)
  ·
    refine ⟨7687682434765969818168055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10250243246354626424224073 7687682434765969818168055)
    ·
      refine ⟨11531523652148954727252083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7687682434765969818168055 11531523652148954727252083)
      ·
        refine ⟨17297285478223432090878125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11531523652148954727252083 17297285478223432090878125)
        ·
          refine ⟨6486482054333787034079297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17297285478223432090878125 6486482054333787034079297)
          ·
            refine ⟨4864861540750340275559473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6486482054333787034079297 4864861540750340275559473)
            ·
              refine ⟨3648646155562755206669605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4864861540750340275559473 3648646155562755206669605)
              ·
                refine ⟨684121154168016601250551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3648646155562755206669605 684121154168016601250551)
                ·
                  refine ⟨1026181731252024901875827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 684121154168016601250551 1026181731252024901875827)
                  ·
                    refine ⟨1539272596878037352813741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1026181731252024901875827 1539272596878037352813741)
                    ·
                      refine ⟨577227223829264007305153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1539272596878037352813741 577227223829264007305153)
                      ·
                        rfl

theorem cell23_1124146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 4, 1, 1, 3].length) (baseStart_1124146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1124146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1124146 prefixEnd_1124146 := by exact prefixLift 1124146
  have htrace : WordTrace (prefixWord ++ tailWord_1124146) baseStart_1124146 baseEnd_1124146 := by
    simpa [prefixWord, tailWord_1124146, baseEnd_1124146] using wordTrace_append hprefix tailTrace_1124146
  have hstable : (prefixWord ++ tailWord_1124146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124146).length < 2 ^ (prefixWord ++ tailWord_1124146).sum := by decide
  have hdescent : baseEnd_1124146 < baseStart_1124146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124165 : List Nat := [1, 3, 1, 1, 1, 2, 5, 1, 1, 1, 6]
def baseStart_1124165 : Nat := 118140960795 + 1124165 * 2 ^ 59
def prefixEnd_1124165 : Nat := 4983230072969 + 3 ^ 40 * 1124165 * 2
def baseEnd_1124165 : Nat := 577236979961699432967565

theorem tailTrace_1124165 : CollatzResearch.WordTrace tailWord_1124165 prefixEnd_1124165 577236979961699432967565 := by
  unfold tailWord_1124165
  simp only [CollatzResearch.WordTrace]
  refine ⟨41001665972349671941837949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27334443981566447961225299 41001665972349671941837949)
  ·
    refine ⟨15375624739631126978189231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41001665972349671941837949 15375624739631126978189231)
    ·
      refine ⟨23063437109446690467283847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15375624739631126978189231 23063437109446690467283847)
      ·
        refine ⟨34595155664170035700925771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23063437109446690467283847 34595155664170035700925771)
        ·
          refine ⟨51892733496255053551388657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34595155664170035700925771 51892733496255053551388657)
          ·
            refine ⟨38919550122191290163541493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51892733496255053551388657 38919550122191290163541493)
            ·
              refine ⟨3648707823955433452832015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38919550122191290163541493 3648707823955433452832015)
              ·
                refine ⟨5473061735933150179248023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3648707823955433452832015 5473061735933150179248023)
                ·
                  refine ⟨8209592603899725268872035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5473061735933150179248023 8209592603899725268872035)
                  ·
                    refine ⟨12314388905849587903308053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8209592603899725268872035 12314388905849587903308053)
                    ·
                      refine ⟨577236979961699432967565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12314388905849587903308053 577236979961699432967565)
                      ·
                        rfl

theorem cell23_1124165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 1, 6].length) (baseStart_1124165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1124165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1124165 prefixEnd_1124165 := by exact prefixLift 1124165
  have htrace : WordTrace (prefixWord ++ tailWord_1124165) baseStart_1124165 baseEnd_1124165 := by
    simpa [prefixWord, tailWord_1124165, baseEnd_1124165] using wordTrace_append hprefix tailTrace_1124165
  have hstable : (prefixWord ++ tailWord_1124165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124165).length < 2 ^ (prefixWord ++ tailWord_1124165).sum := by decide
  have hdescent : baseEnd_1124165 < baseStart_1124165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124166 : List Nat := [6, 1, 1, 2, 1, 1, 1, 4, 1, 5]
def baseStart_1124166 : Nat := 118140960795 + 1124166 * 2 ^ 59
def prefixEnd_1124166 : Nat := 4983230072969 + 3 ^ 40 * 1124166 * 2
def baseEnd_1124166 : Nat := 192412497814117976351687

theorem tailTrace_1124166 : CollatzResearch.WordTrace tailWord_1124166 prefixEnd_1124166 192412497814117976351687 := by
  unfold tailWord_1124166
  simp only [CollatzResearch.WordTrace]
  refine ⟨1281303201417064034769511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 27334468296897366075082901 1281303201417064034769511)
  ·
    refine ⟨1921954802125596052154267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1281303201417064034769511 1921954802125596052154267)
    ·
      refine ⟨2882932203188394078231401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1921954802125596052154267 2882932203188394078231401)
      ·
        refine ⟨2162199152391295558673551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2882932203188394078231401 2162199152391295558673551)
        ·
          refine ⟨3243298728586943338010327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2162199152391295558673551 3243298728586943338010327)
          ·
            refine ⟨4864948092880415007015491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3243298728586943338010327 4864948092880415007015491)
            ·
              refine ⟨7297422139320622510523237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4864948092880415007015491 7297422139320622510523237)
              ·
                refine ⟨1368266651122616720723107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7297422139320622510523237 1368266651122616720723107)
                ·
                  refine ⟨2052399976683925081084661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1368266651122616720723107 2052399976683925081084661)
                  ·
                    refine ⟨192412497814117976351687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2052399976683925081084661 192412497814117976351687)
                    ·
                      rfl

theorem cell23_1124166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_1124166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1124166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1124166 prefixEnd_1124166 := by exact prefixLift 1124166
  have htrace : WordTrace (prefixWord ++ tailWord_1124166) baseStart_1124166 baseEnd_1124166 := by
    simpa [prefixWord, tailWord_1124166, baseEnd_1124166] using wordTrace_append hprefix tailTrace_1124166
  have hstable : (prefixWord ++ tailWord_1124166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124166).length < 2 ^ (prefixWord ++ tailWord_1124166).sum := by decide
  have hdescent : baseEnd_1124166 < baseStart_1124166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124169 : List Nat := [1, 2, 1, 1, 2, 4, 1, 4, 3, 2, 2]
def baseStart_1124169 : Nat := 118140960795 + 1124169 * 2 ^ 59
def prefixEnd_1124169 : Nat := 4983230072969 + 3 ^ 40 * 1124169 * 2
def baseEnd_1124169 : Nat := 577239033884317417317547

theorem tailTrace_1124169 : CollatzResearch.WordTrace tailWord_1124169 prefixEnd_1124169 577239033884317417317547 := by
  unfold tailWord_1124169
  simp only [CollatzResearch.WordTrace]
  refine ⟨41001811864335180624983561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27334541242890120416655707 41001811864335180624983561)
  ·
    refine ⟨30751358898251385468737671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41001811864335180624983561 30751358898251385468737671)
    ·
      refine ⟨46127038347377078203106507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30751358898251385468737671 46127038347377078203106507)
      ·
        refine ⟨69190557521065617304659761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46127038347377078203106507 69190557521065617304659761)
        ·
          refine ⟨51892918140799212978494821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69190557521065617304659761 51892918140799212978494821)
          ·
            refine ⟨9729922151399852433467779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51892918140799212978494821 9729922151399852433467779)
            ·
              refine ⟨14594883227099778650201669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9729922151399852433467779 14594883227099778650201669)
              ·
                refine ⟨2736540605081208496912813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14594883227099778650201669 2736540605081208496912813)
                ·
                  refine ⟨1026202726905453186342305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2736540605081208496912813 1026202726905453186342305)
                  ·
                    refine ⟨769652045179089889756729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1026202726905453186342305 769652045179089889756729)
                    ·
                      refine ⟨577239033884317417317547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 769652045179089889756729 577239033884317417317547)
                      ·
                        rfl

theorem cell23_1124169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 4, 3, 2, 2].length) (baseStart_1124169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1124169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1124169 prefixEnd_1124169 := by exact prefixLift 1124169
  have htrace : WordTrace (prefixWord ++ tailWord_1124169) baseStart_1124169 baseEnd_1124169 := by
    simpa [prefixWord, tailWord_1124169, baseEnd_1124169] using wordTrace_append hprefix tailTrace_1124169
  have hstable : (prefixWord ++ tailWord_1124169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124169).length < 2 ^ (prefixWord ++ tailWord_1124169).sum := by decide
  have hdescent : baseEnd_1124169 < baseStart_1124169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124229 : List Nat := [1, 3, 1, 1, 3, 2, 3, 1, 3, 3, 2]
def baseStart_1124229 : Nat := 118140960795 + 1124229 * 2 ^ 59
def prefixEnd_1124229 : Nat := 4983230072969 + 3 ^ 40 * 1124229 * 2
def baseEnd_1124229 : Nat := 577269842723587182567271

theorem tailTrace_1124229 : CollatzResearch.WordTrace tailWord_1124229 prefixEnd_1124229 577269842723587182567271 := by
  unfold tailWord_1124229
  simp only [CollatzResearch.WordTrace]
  refine ⟨41004000244117810872167741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27336000162745207248111827 41004000244117810872167741)
  ·
    refine ⟨15376500091544179077062903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41004000244117810872167741 15376500091544179077062903)
    ·
      refine ⟨23064750137316268615594355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15376500091544179077062903 23064750137316268615594355)
      ·
        refine ⟨34597125205974402923391533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23064750137316268615594355 34597125205974402923391533)
        ·
          refine ⟨12973921952240401096271825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34597125205974402923391533 12973921952240401096271825)
          ·
            refine ⟨9730441464180300822203869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12973921952240401096271825 9730441464180300822203869)
            ·
              refine ⟨3648915549067612808326451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9730441464180300822203869 3648915549067612808326451)
              ·
                refine ⟨5473373323601419212489677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3648915549067612808326451 5473373323601419212489677)
                ·
                  refine ⟨2052514996350532204683629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5473373323601419212489677 2052514996350532204683629)
                  ·
                    refine ⟨769693123631449576756361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2052514996350532204683629 769693123631449576756361)
                    ·
                      refine ⟨577269842723587182567271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 769693123631449576756361 577269842723587182567271)
                      ·
                        rfl

theorem cell23_1124229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 3, 3, 2].length) (baseStart_1124229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1124229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1124229 prefixEnd_1124229 := by exact prefixLift 1124229
  have htrace : WordTrace (prefixWord ++ tailWord_1124229) baseStart_1124229 baseEnd_1124229 := by
    simpa [prefixWord, tailWord_1124229, baseEnd_1124229] using wordTrace_append hprefix tailTrace_1124229
  have hstable : (prefixWord ++ tailWord_1124229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124229).length < 2 ^ (prefixWord ++ tailWord_1124229).sum := by decide
  have hdescent : baseEnd_1124229 < baseStart_1124229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124235 : List Nat := [1, 1, 1, 1, 4, 2, 1, 2, 4, 6]
def baseStart_1124235 : Nat := 118140960795 + 1124235 * 2 ^ 59
def prefixEnd_1124235 : Nat := 4983230072969 + 3 ^ 40 * 1124235 * 2
def baseEnd_1124235 : Nat := 192424307869171386364081

theorem tailTrace_1124235 : CollatzResearch.WordTrace tailWord_1124235 prefixEnd_1124235 192424307869171386364081 := by
  unfold tailWord_1124235
  simp only [CollatzResearch.WordTrace]
  refine ⟨41004219082096073896886159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27336146054730715931257439 41004219082096073896886159)
  ·
    refine ⟨61506328623144110845329239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41004219082096073896886159 61506328623144110845329239)
    ·
      refine ⟨92259492934716166267993859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61506328623144110845329239 92259492934716166267993859)
      ·
        refine ⟨138389239402074249401990789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92259492934716166267993859 138389239402074249401990789)
        ·
          refine ⟨25947982387888921762873273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 138389239402074249401990789 25947982387888921762873273)
          ·
            refine ⟨19460986790916691322154955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25947982387888921762873273 19460986790916691322154955)
            ·
              refine ⟨29191480186375036983232433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19460986790916691322154955 29191480186375036983232433)
              ·
                refine ⟨21893610139781277737424325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29191480186375036983232433 21893610139781277737424325)
                ·
                  refine ⟨4105051901208989575767061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21893610139781277737424325 4105051901208989575767061)
                  ·
                    refine ⟨192424307869171386364081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4105051901208989575767061 192424307869171386364081)
                    ·
                      rfl

theorem cell23_1124235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 4, 6].length) (baseStart_1124235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1124235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1124235 prefixEnd_1124235 := by exact prefixLift 1124235
  have htrace : WordTrace (prefixWord ++ tailWord_1124235) baseStart_1124235 baseEnd_1124235 := by
    simpa [prefixWord, tailWord_1124235, baseEnd_1124235] using wordTrace_append hprefix tailTrace_1124235
  have hstable : (prefixWord ++ tailWord_1124235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124235).length < 2 ^ (prefixWord ++ tailWord_1124235).sum := by decide
  have hdescent : baseEnd_1124235 < baseStart_1124235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124270 : List Nat := [4, 1, 5, 1, 1, 1, 2, 1, 1, 3, 3]
def baseStart_1124270 : Nat := 118140960795 + 1124270 * 2 ^ 59
def prefixEnd_1124270 : Nat := 4983230072969 + 3 ^ 40 * 1124270 * 2
def baseEnd_1124270 : Nat := 577290895430421522154583

theorem tailTrace_1124270 : CollatzResearch.WordTrace tailWord_1124270 prefixEnd_1124270 577290895430421522154583 := by
  unfold tailWord_1124270
  simp only [CollatzResearch.WordTrace]
  refine ⟨5125686954621159359301283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27336997091312849916273509 5125686954621159359301283)
  ·
    refine ⟨7688530431931739038951925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5125686954621159359301283 7688530431931739038951925)
    ·
      refine ⟨720799727993600534901743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7688530431931739038951925 720799727993600534901743)
      ·
        refine ⟨1081199591990400802352615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 720799727993600534901743 1081199591990400802352615)
        ·
          refine ⟨1621799387985601203528923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1081199591990400802352615 1621799387985601203528923)
          ·
            refine ⟨2432699081978401805293385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1621799387985601203528923 2432699081978401805293385)
            ·
              refine ⟨1824524311483801353970039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2432699081978401805293385 1824524311483801353970039)
              ·
                refine ⟨2736786467225702030955059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1824524311483801353970039 2736786467225702030955059)
                ·
                  refine ⟨4105179700838553046432589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2736786467225702030955059 4105179700838553046432589)
                  ·
                    refine ⟨1539442387814457392412221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4105179700838553046432589 1539442387814457392412221)
                    ·
                      refine ⟨577290895430421522154583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1539442387814457392412221 577290895430421522154583)
                      ·
                        rfl

theorem cell23_1124270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_1124270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1124270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1124270 prefixEnd_1124270 := by exact prefixLift 1124270
  have htrace : WordTrace (prefixWord ++ tailWord_1124270) baseStart_1124270 baseEnd_1124270 := by
    simpa [prefixWord, tailWord_1124270, baseEnd_1124270] using wordTrace_append hprefix tailTrace_1124270
  have hstable : (prefixWord ++ tailWord_1124270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124270).length < 2 ^ (prefixWord ++ tailWord_1124270).sum := by decide
  have hdescent : baseEnd_1124270 < baseStart_1124270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124299 : List Nat := [1, 1, 1, 1, 3, 4, 4, 3, 5]
def baseStart_1124299 : Nat := 118140960795 + 1124299 * 2 ^ 59
def prefixEnd_1124299 : Nat := 4983230072969 + 3 ^ 40 * 1124299 * 2
def baseEnd_1124299 : Nat := 64145087374377989854661

theorem tailTrace_1124299 : CollatzResearch.WordTrace tailWord_1124299 prefixEnd_1124299 64145087374377989854661 := by
  unfold tailWord_1124299
  simp only [CollatzResearch.WordTrace]
  refine ⟨41006553353864212827215951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27337702235909475218143967 41006553353864212827215951)
  ·
    refine ⟨61509830030796319240823927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41006553353864212827215951 61509830030796319240823927)
    ·
      refine ⟨92264745046194478861235891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61509830030796319240823927 92264745046194478861235891)
      ·
        refine ⟨138397117569291718291853837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92264745046194478861235891 138397117569291718291853837)
        ·
          refine ⟨51898919088484394359445189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 138397117569291718291853837 51898919088484394359445189)
          ·
            refine ⟨9731047329090823942395973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51898919088484394359445189 9731047329090823942395973)
            ·
              refine ⟨1824571374204529489199245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9731047329090823942395973 1824571374204529489199245)
              ·
                refine ⟨684214265326698558449717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1824571374204529489199245 684214265326698558449717)
                ·
                  refine ⟨64145087374377989854661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 684214265326698558449717 64145087374377989854661)
                  ·
                    rfl

theorem cell23_1124299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 3, 5].length) (baseStart_1124299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1124299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1124299 prefixEnd_1124299 := by exact prefixLift 1124299
  have htrace : WordTrace (prefixWord ++ tailWord_1124299) baseStart_1124299 baseEnd_1124299 := by
    simpa [prefixWord, tailWord_1124299, baseEnd_1124299] using wordTrace_append hprefix tailTrace_1124299
  have hstable : (prefixWord ++ tailWord_1124299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124299).length < 2 ^ (prefixWord ++ tailWord_1124299).sum := by decide
  have hdescent : baseEnd_1124299 < baseStart_1124299 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124309 : List Nat := [1, 3, 2, 3, 2, 1, 1, 2, 2, 3, 3]
def baseStart_1124309 : Nat := 118140960795 + 1124309 * 2 ^ 59
def prefixEnd_1124309 : Nat := 4983230072969 + 3 ^ 40 * 1124309 * 2
def baseEnd_1124309 : Nat := 577310921175946869566903

theorem tailTrace_1124309 : CollatzResearch.WordTrace tailWord_1124309 prefixEnd_1124309 577310921175946869566903 := by
  unfold tailWord_1124309
  simp only [CollatzResearch.WordTrace]
  refine ⟨41006918083827984535079981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27337945389218656356719987 41006918083827984535079981)
  ·
    refine ⟨15377594281435494200654993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41006918083827984535079981 15377594281435494200654993)
    ·
      refine ⟨11533195711076620650491245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15377594281435494200654993 11533195711076620650491245)
      ·
        refine ⟨4324948391653732743934217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11533195711076620650491245 4324948391653732743934217)
        ·
          refine ⟨3243711293740299557950663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4324948391653732743934217 3243711293740299557950663)
          ·
            refine ⟨4865566940610449336925995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3243711293740299557950663 4865566940610449336925995)
            ·
              refine ⟨7298350410915674005388993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4865566940610449336925995 7298350410915674005388993)
              ·
                refine ⟨5473762808186755504041745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7298350410915674005388993 5473762808186755504041745)
                ·
                  refine ⟨4105322106140066628031309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5473762808186755504041745 4105322106140066628031309)
                  ·
                    refine ⟨1539495789802524985511741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4105322106140066628031309 1539495789802524985511741)
                    ·
                      refine ⟨577310921175946869566903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1539495789802524985511741 577310921175946869566903)
                      ·
                        rfl

theorem cell23_1124309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_1124309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1124309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1124309 prefixEnd_1124309 := by exact prefixLift 1124309
  have htrace : WordTrace (prefixWord ++ tailWord_1124309) baseStart_1124309 baseEnd_1124309 := by
    simpa [prefixWord, tailWord_1124309, baseEnd_1124309] using wordTrace_append hprefix tailTrace_1124309
  have hstable : (prefixWord ++ tailWord_1124309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124309).length < 2 ^ (prefixWord ++ tailWord_1124309).sum := by decide
  have hdescent : baseEnd_1124309 < baseStart_1124309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124310 : List Nat := [5, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2]
def baseStart_1124310 : Nat := 118140960795 + 1124310 * 2 ^ 59
def prefixEnd_1124310 : Nat := 4983230072969 + 3 ^ 40 * 1124310 * 2
def baseEnd_1124310 : Nat := 577311434656601365654399

theorem tailTrace_1124310 : CollatzResearch.WordTrace tailWord_1124310 prefixEnd_1124310 577311434656601365654399 := by
  unfold tailWord_1124310
  simp only [CollatzResearch.WordTrace]
  refine ⟨2562934659801522606616649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27337969704549574470577589 2562934659801522606616649)
  ·
    refine ⟨1922200994851141954962487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2562934659801522606616649 1922200994851141954962487)
    ·
      refine ⟨2883301492276712932443731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1922200994851141954962487 2883301492276712932443731)
      ·
        refine ⟨4324952238415069398665597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2883301492276712932443731 4324952238415069398665597)
        ·
          refine ⟨1621857089405651024499599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4324952238415069398665597 1621857089405651024499599)
          ·
            refine ⟨2432785634108476536749399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1621857089405651024499599 2432785634108476536749399)
            ·
              refine ⟨3649178451162714805124099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2432785634108476536749399 3649178451162714805124099)
              ·
                refine ⟨5473767676744072207686149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3649178451162714805124099 5473767676744072207686149)
                ·
                  refine ⟨1026331439389513538941153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5473767676744072207686149 1026331439389513538941153)
                  ·
                    refine ⟨769748579542135154205865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1026331439389513538941153 769748579542135154205865)
                    ·
                      refine ⟨577311434656601365654399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 769748579542135154205865 577311434656601365654399)
                      ·
                        rfl

theorem cell23_1124310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2].length) (baseStart_1124310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1124310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1124310 prefixEnd_1124310 := by exact prefixLift 1124310
  have htrace : WordTrace (prefixWord ++ tailWord_1124310) baseStart_1124310 baseEnd_1124310 := by
    simpa [prefixWord, tailWord_1124310, baseEnd_1124310] using wordTrace_append hprefix tailTrace_1124310
  have hstable : (prefixWord ++ tailWord_1124310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124310).length < 2 ^ (prefixWord ++ tailWord_1124310).sum := by decide
  have hdescent : baseEnd_1124310 < baseStart_1124310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124312 : List Nat := [2, 1, 2, 2, 2, 2, 2, 1, 4, 5]
def baseStart_1124312 : Nat := 118140960795 + 1124312 * 2 ^ 59
def prefixEnd_1124312 : Nat := 4983230072969 + 3 ^ 40 * 1124312 * 2
def baseEnd_1124312 : Nat := 192437487205970119276463

theorem tailTrace_1124312 : CollatzResearch.WordTrace tailWord_1124312 prefixEnd_1124312 192437487205970119276463 := by
  unfold tailWord_1124312
  simp only [CollatzResearch.WordTrace]
  refine ⟨20503513751408558023719595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27338018335211410698292793 20503513751408558023719595)
  ·
    refine ⟨30755270627112837035579393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20503513751408558023719595 30755270627112837035579393)
    ·
      refine ⟨23066452970334627776684545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30755270627112837035579393 23066452970334627776684545)
      ·
        refine ⟨17299839727750970832513409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23066452970334627776684545 17299839727750970832513409)
        ·
          refine ⟨12974879795813228124385057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17299839727750970832513409 12974879795813228124385057)
          ·
            refine ⟨9731159846859921093288793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12974879795813228124385057 9731159846859921093288793)
            ·
              refine ⟨7298369885144940819966595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9731159846859921093288793 7298369885144940819966595)
              ·
                refine ⟨10947554827717411229949893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7298369885144940819966595 10947554827717411229949893)
                ·
                  refine ⟨2052666530197014605615605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10947554827717411229949893 2052666530197014605615605)
                  ·
                    refine ⟨192437487205970119276463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2052666530197014605615605 192437487205970119276463)
                    ·
                      rfl

theorem cell23_1124312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 4, 5].length) (baseStart_1124312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1124312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1124312 prefixEnd_1124312 := by exact prefixLift 1124312
  have htrace : WordTrace (prefixWord ++ tailWord_1124312) baseStart_1124312 baseEnd_1124312 := by
    simpa [prefixWord, tailWord_1124312, baseEnd_1124312] using wordTrace_append hprefix tailTrace_1124312
  have hstable : (prefixWord ++ tailWord_1124312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124312).length < 2 ^ (prefixWord ++ tailWord_1124312).sum := by decide
  have hdescent : baseEnd_1124312 < baseStart_1124312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124349 : List Nat := [1, 4, 1, 1, 1, 2, 2, 2, 1, 6, 2]
def baseStart_1124349 : Nat := 118140960795 + 1124349 * 2 ^ 59
def prefixEnd_1124349 : Nat := 4983230072969 + 3 ^ 40 * 1124349 * 2
def baseEnd_1124349 : Nat := 577331460402126713066719

theorem tailTrace_1124349 : CollatzResearch.WordTrace tailWord_1124349 prefixEnd_1124349 577331460402126713066719 := by
  unfold tailWord_1124349
  simp only [CollatzResearch.WordTrace]
  refine ⟨41008377003683071366536101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27338918002455380911024067 41008377003683071366536101)
  ·
    refine ⟨7689070688190575881225519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41008377003683071366536101 7689070688190575881225519)
    ·
      refine ⟨11533606032285863821838279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7689070688190575881225519 11533606032285863821838279)
      ·
        refine ⟨17300409048428795732757419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11533606032285863821838279 17300409048428795732757419)
        ·
          refine ⟨25950613572643193599136129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17300409048428795732757419 25950613572643193599136129)
          ·
            refine ⟨19462960179482395199352097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25950613572643193599136129 19462960179482395199352097)
            ·
              refine ⟨14597220134611796399514073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19462960179482395199352097 14597220134611796399514073)
              ·
                refine ⟨10947915100958847299635555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14597220134611796399514073 10947915100958847299635555)
                ·
                  refine ⟨16421872651438270949453333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10947915100958847299635555 16421872651438270949453333)
                  ·
                    refine ⟨769775280536168950755625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16421872651438270949453333 769775280536168950755625)
                    ·
                      refine ⟨577331460402126713066719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 769775280536168950755625 577331460402126713066719)
                      ·
                        rfl

theorem cell23_1124349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 6, 2].length) (baseStart_1124349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1124349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1124349 prefixEnd_1124349 := by exact prefixLift 1124349
  have htrace : WordTrace (prefixWord ++ tailWord_1124349) baseStart_1124349 baseEnd_1124349 := by
    simpa [prefixWord, tailWord_1124349, baseEnd_1124349] using wordTrace_append hprefix tailTrace_1124349
  have hstable : (prefixWord ++ tailWord_1124349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124349).length < 2 ^ (prefixWord ++ tailWord_1124349).sum := by decide
  have hdescent : baseEnd_1124349 < baseStart_1124349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124389 : List Nat := [1, 3, 1, 2, 2, 4, 1, 3, 6]
def baseStart_1124389 : Nat := 118140960795 + 1124389 * 2 ^ 59
def prefixEnd_1124389 : Nat := 4983230072969 + 3 ^ 40 * 1124389 * 2
def baseEnd_1124389 : Nat := 64150222180922950729615

theorem tailTrace_1124389 : CollatzResearch.WordTrace tailWord_1124389 prefixEnd_1124389 64150222180922950729615 := by
  unfold tailWord_1124389
  simp only [CollatzResearch.WordTrace]
  refine ⟨41009835923538158197992221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27339890615692105465328147 41009835923538158197992221)
  ·
    refine ⟨15378688471326809324247083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41009835923538158197992221 15378688471326809324247083)
    ·
      refine ⟨23068032706990213986370625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15378688471326809324247083 23068032706990213986370625)
      ·
        refine ⟨17301024530242660489777969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23068032706990213986370625 17301024530242660489777969)
        ·
          refine ⟨12975768397681995367333477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17301024530242660489777969 12975768397681995367333477)
          ·
            refine ⟨2432956574565374131375027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12975768397681995367333477 2432956574565374131375027)
            ·
              refine ⟨3649434861848061197062541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2432956574565374131375027 3649434861848061197062541)
              ·
                refine ⟨1368538073193022948898453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3649434861848061197062541 1368538073193022948898453)
                ·
                  refine ⟨64150222180922950729615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1368538073193022948898453 64150222180922950729615)
                  ·
                    rfl

theorem cell23_1124389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 3, 6].length) (baseStart_1124389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1124389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1124389 prefixEnd_1124389 := by exact prefixLift 1124389
  have htrace : WordTrace (prefixWord ++ tailWord_1124389) baseStart_1124389 baseEnd_1124389 := by
    simpa [prefixWord, tailWord_1124389, baseEnd_1124389] using wordTrace_append hprefix tailTrace_1124389
  have hstable : (prefixWord ++ tailWord_1124389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124389).length < 2 ^ (prefixWord ++ tailWord_1124389).sum := by decide
  have hdescent : baseEnd_1124389 < baseStart_1124389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124439 : List Nat := [1, 1, 3, 2, 2, 1, 3, 2, 3, 1, 4]
def baseStart_1124439 : Nat := 118140960795 + 1124439 * 2 ^ 59
def prefixEnd_1124439 : Nat := 4983230072969 + 3 ^ 40 * 1124439 * 2
def baseEnd_1124439 : Nat := 577377673661031360941305

theorem tailTrace_1124439 : CollatzResearch.WordTrace tailWord_1124439 prefixEnd_1124439 577377673661031360941305 := by
  unfold tailWord_1124439
  simp only [CollatzResearch.WordTrace]
  refine ⟨41011659573357016737312371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27341106382238011158208247 41011659573357016737312371)
  ·
    refine ⟨61517489360035525105968557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41011659573357016737312371 61517489360035525105968557)
    ·
      refine ⟨23069058510013321914738209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61517489360035525105968557 23069058510013321914738209)
      ·
        refine ⟨17301793882509991436053657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23069058510013321914738209 17301793882509991436053657)
        ·
          refine ⟨12976345411882493577040243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17301793882509991436053657 12976345411882493577040243)
          ·
            refine ⟨19464518117823740365560365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12976345411882493577040243 19464518117823740365560365)
            ·
              refine ⟨7299194294183902637085137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19464518117823740365560365 7299194294183902637085137)
              ·
                refine ⟨5474395720637926977813853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7299194294183902637085137 5474395720637926977813853)
                ·
                  refine ⟨2052898395239222616680195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5474395720637926977813853 2052898395239222616680195)
                  ·
                    refine ⟨3079347592858833925020293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2052898395239222616680195 3079347592858833925020293)
                    ·
                      refine ⟨577377673661031360941305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3079347592858833925020293 577377673661031360941305)
                      ·
                        rfl

theorem cell23_1124439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 3, 1, 4].length) (baseStart_1124439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1124439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1124439 prefixEnd_1124439 := by exact prefixLift 1124439
  have htrace : WordTrace (prefixWord ++ tailWord_1124439) baseStart_1124439 baseEnd_1124439 := by
    simpa [prefixWord, tailWord_1124439, baseEnd_1124439] using wordTrace_append hprefix tailTrace_1124439
  have hstable : (prefixWord ++ tailWord_1124439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124439).length < 2 ^ (prefixWord ++ tailWord_1124439).sum := by decide
  have hdescent : baseEnd_1124439 < baseStart_1124439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124449 : List Nat := [1, 2, 3, 1, 1, 2, 1, 2, 6, 4]
def baseStart_1124449 : Nat := 118140960795 + 1124449 * 2 ^ 59
def prefixEnd_1124449 : Nat := 4983230072969 + 3 ^ 40 * 1124449 * 2
def baseEnd_1124449 : Nat := 192460936155858773938753

theorem tailTrace_1124449 : CollatzResearch.WordTrace tailWord_1124449 prefixEnd_1124449 192460936155858773938753 := by
  unfold tailWord_1124449
  simp only [CollatzResearch.WordTrace]
  refine ⟨41012024303320788445176401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27341349535547192296784267 41012024303320788445176401)
  ·
    refine ⟨30759018227490591333882301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41012024303320788445176401 30759018227490591333882301)
    ·
      refine ⟨11534631835308971750205863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30759018227490591333882301 11534631835308971750205863)
      ·
        refine ⟨17301947752963457625308795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11534631835308971750205863 17301947752963457625308795)
        ·
          refine ⟨25952921629445186437963193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17301947752963457625308795 25952921629445186437963193)
          ·
            refine ⟨19464691222083889828472395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25952921629445186437963193 19464691222083889828472395)
            ·
              refine ⟨29197036833125834742708593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19464691222083889828472395 29197036833125834742708593)
              ·
                refine ⟨21897777624844376057031445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29197036833125834742708593 21897777624844376057031445)
                ·
                  refine ⟨1026458326164580127673349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 21897777624844376057031445 1026458326164580127673349)
                  ·
                    refine ⟨192460936155858773938753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1026458326164580127673349 192460936155858773938753)
                    ·
                      rfl

theorem cell23_1124449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 6, 4].length) (baseStart_1124449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1124449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1124449 prefixEnd_1124449 := by exact prefixLift 1124449
  have htrace : WordTrace (prefixWord ++ tailWord_1124449) baseStart_1124449 baseEnd_1124449 := by
    simpa [prefixWord, tailWord_1124449, baseEnd_1124449] using wordTrace_append hprefix tailTrace_1124449
  have hstable : (prefixWord ++ tailWord_1124449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124449).length < 2 ^ (prefixWord ++ tailWord_1124449).sum := by decide
  have hdescent : baseEnd_1124449 < baseStart_1124449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124450 : List Nat := [3, 3, 2, 2, 2, 1, 1, 2, 3, 1, 3]
def baseStart_1124450 : Nat := 118140960795 + 1124450 * 2 ^ 59
def prefixEnd_1124450 : Nat := 4983230072969 + 3 ^ 40 * 1124450 * 2
def baseEnd_1124450 : Nat := 577383321948230817903755

theorem tailTrace_1124450 : CollatzResearch.WordTrace tailWord_1124450 prefixEnd_1124450 577383321948230817903755 := by
  unfold tailWord_1124450
  simp only [CollatzResearch.WordTrace]
  refine ⟨10253015194079291403990701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27341373850878110410641869 10253015194079291403990701)
  ·
    refine ⟨3844880697779734276496513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10253015194079291403990701 3844880697779734276496513)
    ·
      refine ⟨2883660523334800707372385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3844880697779734276496513 2883660523334800707372385)
      ·
        refine ⟨2162745392501100530529289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2883660523334800707372385 2162745392501100530529289)
        ·
          refine ⟨1622059044375825397896967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2162745392501100530529289 1622059044375825397896967)
          ·
            refine ⟨2433088566563738096845451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1622059044375825397896967 2433088566563738096845451)
            ·
              refine ⟨3649632849845607145268177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2433088566563738096845451 3649632849845607145268177)
              ·
                refine ⟨2737224637384205358951133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3649632849845607145268177 2737224637384205358951133)
                ·
                  refine ⟨1026459239019077009606675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2737224637384205358951133 1026459239019077009606675)
                  ·
                    refine ⟨1539688858528615514410013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1026459239019077009606675 1539688858528615514410013)
                    ·
                      refine ⟨577383321948230817903755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1539688858528615514410013 577383321948230817903755)
                      ·
                        rfl

theorem cell23_1124450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_1124450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1124450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1124450 prefixEnd_1124450 := by exact prefixLift 1124450
  have htrace : WordTrace (prefixWord ++ tailWord_1124450) baseStart_1124450 baseEnd_1124450 := by
    simpa [prefixWord, tailWord_1124450, baseEnd_1124450] using wordTrace_append hprefix tailTrace_1124450
  have hstable : (prefixWord ++ tailWord_1124450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124450).length < 2 ^ (prefixWord ++ tailWord_1124450).sum := by decide
  have hdescent : baseEnd_1124450 < baseStart_1124450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124470 : List Nat := [5, 1, 1, 2, 1, 4, 2, 1, 1, 5]
def baseStart_1124470 : Nat := 118140960795 + 1124470 * 2 ^ 59
def prefixEnd_1124470 : Nat := 4983230072969 + 3 ^ 40 * 1124470 * 2
def baseEnd_1124470 : Nat := 192464530520440246551221

theorem tailTrace_1124470 : CollatzResearch.WordTrace tailWord_1124470 prefixEnd_1124470 192464530520440246551221 := by
  unfold tailWord_1124470
  simp only [CollatzResearch.WordTrace]
  refine ⟨2563299389765294314480679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27341860157496472687793909 2563299389765294314480679)
  ·
    refine ⟨3844949084647941471721019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2563299389765294314480679 3844949084647941471721019)
    ·
      refine ⟨5767423626971912207581529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3844949084647941471721019 5767423626971912207581529)
      ·
        refine ⟨4325567720228934155686147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5767423626971912207581529 4325567720228934155686147)
        ·
          refine ⟨6488351580343401233529221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4325567720228934155686147 6488351580343401233529221)
          ·
            refine ⟨1216565921314387731286729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6488351580343401233529221 1216565921314387731286729)
            ·
              refine ⟨912424440985790798465047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1216565921314387731286729 912424440985790798465047)
              ·
                refine ⟨1368636661478686197697571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 912424440985790798465047 1368636661478686197697571)
                ·
                  refine ⟨2052954992218029296546357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1368636661478686197697571 2052954992218029296546357)
                  ·
                    refine ⟨192464530520440246551221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2052954992218029296546357 192464530520440246551221)
                    ·
                      rfl

theorem cell23_1124470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 2, 1, 1, 5].length) (baseStart_1124470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1124470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1124470 prefixEnd_1124470 := by exact prefixLift 1124470
  have htrace : WordTrace (prefixWord ++ tailWord_1124470) baseStart_1124470 baseEnd_1124470 := by
    simpa [prefixWord, tailWord_1124470, baseEnd_1124470] using wordTrace_append hprefix tailTrace_1124470
  have hstable : (prefixWord ++ tailWord_1124470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124470).length < 2 ^ (prefixWord ++ tailWord_1124470).sum := by decide
  have hdescent : baseEnd_1124470 < baseStart_1124470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124473 : List Nat := [1, 2, 1, 3, 4, 1, 4, 1, 1, 1, 4]
def baseStart_1124473 : Nat := 118140960795 + 1124473 * 2 ^ 59
def prefixEnd_1124473 : Nat := 4983230072969 + 3 ^ 40 * 1124473 * 2
def baseEnd_1124473 : Nat := 577395132003284227916149

theorem tailTrace_1124473 : CollatzResearch.WordTrace tailWord_1124473 prefixEnd_1124473 577395132003284227916149 := by
  unfold tailWord_1124473
  simp only [CollatzResearch.WordTrace]
  refine ⟨41012899655233840544050073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27341933103489227029366715 41012899655233840544050073)
  ·
    refine ⟨30759674741425380408037555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41012899655233840544050073 30759674741425380408037555)
    ·
      refine ⟨46139512112138070612056333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30759674741425380408037555 46139512112138070612056333)
      ·
        refine ⟨17302317042051776479521125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46139512112138070612056333 17302317042051776479521125)
        ·
          refine ⟨3244184445384708089910211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17302317042051776479521125 3244184445384708089910211)
          ·
            refine ⟨4866276668077062134865317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3244184445384708089910211 4866276668077062134865317)
            ·
              refine ⟨912426875264449150287247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4866276668077062134865317 912426875264449150287247)
              ·
                refine ⟨1368640312896673725430871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 912426875264449150287247 1368640312896673725430871)
                ·
                  refine ⟨2052960469345010588146307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1368640312896673725430871 2052960469345010588146307)
                  ·
                    refine ⟨3079440704017515882219461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2052960469345010588146307 3079440704017515882219461)
                    ·
                      refine ⟨577395132003284227916149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3079440704017515882219461 577395132003284227916149)
                      ·
                        rfl

theorem cell23_1124473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 4, 1, 1, 1, 4].length) (baseStart_1124473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1124473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1124473 prefixEnd_1124473 := by exact prefixLift 1124473
  have htrace : WordTrace (prefixWord ++ tailWord_1124473) baseStart_1124473 baseEnd_1124473 := by
    simpa [prefixWord, tailWord_1124473, baseEnd_1124473] using wordTrace_append hprefix tailTrace_1124473
  have hstable : (prefixWord ++ tailWord_1124473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124473).length < 2 ^ (prefixWord ++ tailWord_1124473).sum := by decide
  have hdescent : baseEnd_1124473 < baseStart_1124473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124483 : List Nat := [1, 1, 1, 3, 3, 5, 1, 2, 2, 4]
def baseStart_1124483 : Nat := 118140960795 + 1124483 * 2 ^ 59
def prefixEnd_1124483 : Nat := 4983230072969 + 3 ^ 40 * 1124483 * 2
def baseEnd_1124483 : Nat := 192466755603276396263701

theorem tailTrace_1124483 : CollatzResearch.WordTrace tailWord_1124483 prefixEnd_1124483 192466755603276396263701 := by
  unfold tailWord_1124483
  simp only [CollatzResearch.WordTrace]
  refine ⟨41013264385197612251914103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27342176256798408167942735 41013264385197612251914103)
  ·
    refine ⟨61519896577796418377871155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41013264385197612251914103 61519896577796418377871155)
    ·
      refine ⟨92279844866694627566806733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61519896577796418377871155 92279844866694627566806733)
      ·
        refine ⟨34604941825010485337552525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92279844866694627566806733 34604941825010485337552525)
        ·
          refine ⟨12976853184378932001582197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34604941825010485337552525 12976853184378932001582197)
          ·
            refine ⟨1216579986035524875148331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12976853184378932001582197 1216579986035524875148331)
            ·
              refine ⟨1824869979053287312722497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1216579986035524875148331 1824869979053287312722497)
              ·
                refine ⟨1368652484289965484541873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1824869979053287312722497 1368652484289965484541873)
                ·
                  refine ⟨1026489363217474113406405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1368652484289965484541873 1026489363217474113406405)
                  ·
                    refine ⟨192466755603276396263701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1026489363217474113406405 192466755603276396263701)
                    ·
                      rfl

theorem cell23_1124483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 2, 2, 4].length) (baseStart_1124483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1124483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1124483 prefixEnd_1124483 := by exact prefixLift 1124483
  have htrace : WordTrace (prefixWord ++ tailWord_1124483) baseStart_1124483 baseEnd_1124483 := by
    simpa [prefixWord, tailWord_1124483, baseEnd_1124483] using wordTrace_append hprefix tailTrace_1124483
  have hstable : (prefixWord ++ tailWord_1124483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124483).length < 2 ^ (prefixWord ++ tailWord_1124483).sum := by decide
  have hdescent : baseEnd_1124483 < baseStart_1124483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124490 : List Nat := [3, 1, 2, 3, 1, 3, 2, 1, 3, 2, 2]
def baseStart_1124490 : Nat := 118140960795 + 1124490 * 2 ^ 59
def prefixEnd_1124490 : Nat := 4983230072969 + 3 ^ 40 * 1124490 * 2
def baseEnd_1124490 : Nat := 577403861174410661403571

theorem tailTrace_1124490 : CollatzResearch.WordTrace tailWord_1124490 prefixEnd_1124490 577403861174410661403571 := by
  unfold tailWord_1124490
  simp only [CollatzResearch.WordTrace]
  refine ⟨10253379924043063111854731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27342346464114834964945949 10253379924043063111854731)
  ·
    refine ⟨15380069886064594667782097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10253379924043063111854731 15380069886064594667782097)
    ·
      refine ⟨11535052414548446000836573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15380069886064594667782097 11535052414548446000836573)
      ·
        refine ⟨4325644655455667250313715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11535052414548446000836573 4325644655455667250313715)
        ·
          refine ⟨6488466983183500875470573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4325644655455667250313715 6488466983183500875470573)
          ·
            refine ⟨2433175118693812828301465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6488466983183500875470573 2433175118693812828301465)
            ·
              refine ⟨1824881339020359621226099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2433175118693812828301465 1824881339020359621226099)
              ·
                refine ⟨2737322008530539431839149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1824881339020359621226099 2737322008530539431839149)
                ·
                  refine ⟨1026495753198952286939681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2737322008530539431839149 1026495753198952286939681)
                  ·
                    refine ⟨769871814899214215204761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1026495753198952286939681 769871814899214215204761)
                    ·
                      refine ⟨577403861174410661403571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 769871814899214215204761 577403861174410661403571)
                      ·
                        rfl

theorem cell23_1124490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 1, 3, 2, 2].length) (baseStart_1124490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1124490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1124490 prefixEnd_1124490 := by exact prefixLift 1124490
  have htrace : WordTrace (prefixWord ++ tailWord_1124490) baseStart_1124490 baseEnd_1124490 := by
    simpa [prefixWord, tailWord_1124490, baseEnd_1124490] using wordTrace_append hprefix tailTrace_1124490
  have hstable : (prefixWord ++ tailWord_1124490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124490).length < 2 ^ (prefixWord ++ tailWord_1124490).sum := by decide
  have hdescent : baseEnd_1124490 < baseStart_1124490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124500 : List Nat := [2, 4, 2, 3, 1, 2, 1, 1, 1, 6]
def baseStart_1124500 : Nat := 118140960795 + 1124500 * 2 ^ 59
def prefixEnd_1124500 : Nat := 4983230072969 + 3 ^ 40 * 1124500 * 2
def baseEnd_1124500 : Nat := 192469665326985207426175

theorem tailTrace_1124500 : CollatzResearch.WordTrace tailWord_1124500 prefixEnd_1124500 192469665326985207426175 := by
  unfold tailWord_1124500
  simp only [CollatzResearch.WordTrace]
  refine ⟨20506942213068012077641477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27342589617424016103521969 20506942213068012077641477)
  ·
    refine ⟨3845051664950252264557777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20506942213068012077641477 3845051664950252264557777)
    ·
      refine ⟨2883788748712689198418333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3845051664950252264557777 2883788748712689198418333)
      ·
        refine ⟨1081420780767258449406875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2883788748712689198418333 1081420780767258449406875)
        ·
          refine ⟨1622131171150887674110313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1081420780767258449406875 1622131171150887674110313)
          ·
            refine ⟨1216598378363165755582735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1622131171150887674110313 1216598378363165755582735)
            ·
              refine ⟨1824897567544748633374103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1216598378363165755582735 1824897567544748633374103)
              ·
                refine ⟨2737346351317122950061155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1824897567544748633374103 2737346351317122950061155)
                ·
                  refine ⟨4106019526975684425091733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2737346351317122950061155 4106019526975684425091733)
                  ·
                    refine ⟨192469665326985207426175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4106019526975684425091733 192469665326985207426175)
                    ·
                      rfl

theorem cell23_1124500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_1124500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1124500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1124500 prefixEnd_1124500 := by exact prefixLift 1124500
  have htrace : WordTrace (prefixWord ++ tailWord_1124500) baseStart_1124500 baseEnd_1124500 := by
    simpa [prefixWord, tailWord_1124500, baseEnd_1124500] using wordTrace_append hprefix tailTrace_1124500
  have hstable : (prefixWord ++ tailWord_1124500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124500).length < 2 ^ (prefixWord ++ tailWord_1124500).sum := by decide
  have hdescent : baseEnd_1124500 < baseStart_1124500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124503 : List Nat := [1, 1, 3, 3, 4, 2, 1, 1, 1, 2, 4]
def baseStart_1124503 : Nat := 118140960795 + 1124503 * 2 ^ 59
def prefixEnd_1124503 : Nat := 4983230072969 + 3 ^ 40 * 1124503 * 2
def baseEnd_1124503 : Nat := 577410536422919110541011

theorem tailTrace_1124503 : CollatzResearch.WordTrace tailWord_1124503 prefixEnd_1124503 577410536422919110541011 := by
  unfold tailWord_1124503
  simp only [CollatzResearch.WordTrace]
  refine ⟨41013993845125155667642163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27342662563416770445094775 41013993845125155667642163)
  ·
    refine ⟨61520990767687733501463245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41013993845125155667642163 61520990767687733501463245)
    ·
      refine ⟨23070371537882900063048717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61520990767687733501463245 23070371537882900063048717)
      ·
        refine ⟨8651389326706087523643269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23070371537882900063048717 8651389326706087523643269)
        ·
          refine ⟨1622135498757391410683113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8651389326706087523643269 1622135498757391410683113)
          ·
            refine ⟨1216601624068043558012335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1622135498757391410683113 1216601624068043558012335)
            ·
              refine ⟨1824902436102065337018503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1216601624068043558012335 1824902436102065337018503)
              ·
                refine ⟨2737353654153098005527755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1824902436102065337018503 2737353654153098005527755)
                ·
                  refine ⟨4106030481229647008291633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2737353654153098005527755 4106030481229647008291633)
                  ·
                    refine ⟨3079522860922235256218725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4106030481229647008291633 3079522860922235256218725)
                    ·
                      refine ⟨577410536422919110541011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3079522860922235256218725 577410536422919110541011)
                      ·
                        rfl

theorem cell23_1124503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 1, 1, 2, 4].length) (baseStart_1124503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1124503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1124503 prefixEnd_1124503 := by exact prefixLift 1124503
  have htrace : WordTrace (prefixWord ++ tailWord_1124503) baseStart_1124503 baseEnd_1124503 := by
    simpa [prefixWord, tailWord_1124503, baseEnd_1124503] using wordTrace_append hprefix tailTrace_1124503
  have hstable : (prefixWord ++ tailWord_1124503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124503).length < 2 ^ (prefixWord ++ tailWord_1124503).sum := by decide
  have hdescent : baseEnd_1124503 < baseStart_1124503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124559 : List Nat := [1, 1, 2, 1, 1, 3, 4, 1, 1, 4, 4]
def baseStart_1124559 : Nat := 118140960795 + 1124559 * 2 ^ 59
def prefixEnd_1124559 : Nat := 4983230072969 + 3 ^ 40 * 1124559 * 2
def baseEnd_1124559 : Nat := 577439291339570891440753

theorem tailTrace_1124559 : CollatzResearch.WordTrace tailWord_1124559 prefixEnd_1124559 577439291339570891440753 := by
  unfold tailWord_1124559
  simp only [CollatzResearch.WordTrace]
  refine ⟨41016036332922277231680731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27344024221948184821120487 41016036332922277231680731)
  ·
    refine ⟨61524054499383415847521097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41016036332922277231680731 61524054499383415847521097)
    ·
      refine ⟨46143040874537561885640823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61524054499383415847521097 46143040874537561885640823)
      ·
        refine ⟨69214561311806342828461235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46143040874537561885640823 69214561311806342828461235)
        ·
          refine ⟨103821841967709514242691853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69214561311806342828461235 103821841967709514242691853)
          ·
            refine ⟨38933190737891067841009445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103821841967709514242691853 38933190737891067841009445)
            ·
              refine ⟨7299973263354575220189271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38933190737891067841009445 7299973263354575220189271)
              ·
                refine ⟨10949959895031862830283907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7299973263354575220189271 10949959895031862830283907)
                ·
                  refine ⟨16424939842547794245425861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10949959895031862830283907 16424939842547794245425861)
                  ·
                    refine ⟨3079676220477711421017349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16424939842547794245425861 3079676220477711421017349)
                    ·
                      refine ⟨577439291339570891440753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3079676220477711421017349 577439291339570891440753)
                      ·
                        rfl

theorem cell23_1124559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 4, 4].length) (baseStart_1124559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1124559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1124559 prefixEnd_1124559 := by exact prefixLift 1124559
  have htrace : WordTrace (prefixWord ++ tailWord_1124559) baseStart_1124559 baseEnd_1124559 := by
    simpa [prefixWord, tailWord_1124559, baseEnd_1124559] using wordTrace_append hprefix tailTrace_1124559
  have hstable : (prefixWord ++ tailWord_1124559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124559).length < 2 ^ (prefixWord ++ tailWord_1124559).sum := by decide
  have hdescent : baseEnd_1124559 < baseStart_1124559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124569 : List Nat := [1, 2, 1, 2, 3, 1, 2, 4, 7]
def baseStart_1124569 : Nat := 118140960795 + 1124569 * 2 ^ 59
def prefixEnd_1124569 : Nat := 4983230072969 + 3 ^ 40 * 1124569 * 2
def baseEnd_1124569 : Nat := 64160491794012872479523

theorem tailTrace_1124569 : CollatzResearch.WordTrace tailWord_1124569 prefixEnd_1124569 64160491794012872479523 := by
  unfold tailWord_1124569
  simp only [CollatzResearch.WordTrace]
  refine ⟨41016401062886048939544761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27344267375257365959696507 41016401062886048939544761)
  ·
    refine ⟨30762300797164536704658571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41016401062886048939544761 30762300797164536704658571)
    ·
      refine ⟨46143451195746805056987857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30762300797164536704658571 46143451195746805056987857)
      ·
        refine ⟨34607588396810103792740893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46143451195746805056987857 34607588396810103792740893)
        ·
          refine ⟨12977845648803788922277835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34607588396810103792740893 12977845648803788922277835)
          ·
            refine ⟨19466768473205683383416753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12977845648803788922277835 19466768473205683383416753)
            ·
              refine ⟨14600076354904262537562565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19466768473205683383416753 14600076354904262537562565)
              ·
                refine ⟨2737514316544549225792981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14600076354904262537562565 2737514316544549225792981)
                ·
                  refine ⟨64160491794012872479523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2737514316544549225792981 64160491794012872479523)
                  ·
                    rfl

theorem cell23_1124569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 4, 7].length) (baseStart_1124569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1124569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1124569 prefixEnd_1124569 := by exact prefixLift 1124569
  have htrace : WordTrace (prefixWord ++ tailWord_1124569) baseStart_1124569 baseEnd_1124569 := by
    simpa [prefixWord, tailWord_1124569, baseEnd_1124569] using wordTrace_append hprefix tailTrace_1124569
  have hstable : (prefixWord ++ tailWord_1124569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124569).length < 2 ^ (prefixWord ++ tailWord_1124569).sum := by decide
  have hdescent : baseEnd_1124569 < baseStart_1124569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124670 : List Nat := [4, 2, 1, 2, 1, 2, 2, 1, 2, 4, 2]
def baseStart_1124670 : Nat := 118140960795 + 1124670 * 2 ^ 59
def prefixEnd_1124670 : Nat := 4983230072969 + 3 ^ 40 * 1124670 * 2
def baseEnd_1124670 : Nat := 577496287692219957152743

theorem tailTrace_1124670 : CollatzResearch.WordTrace tailWord_1124670 prefixEnd_1124670 577496287692219957152743 := by
  unfold tailWord_1124670
  simp only [CollatzResearch.WordTrace]
  refine ⟨5127510604440017898621433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27346723223680095459314309 5127510604440017898621433)
  ·
    refine ⟨3845632953330013423966075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5127510604440017898621433 3845632953330013423966075)
    ·
      refine ⟨5768449429995020135949113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3845632953330013423966075 5768449429995020135949113)
      ·
        refine ⟨4326337072496265101961835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5768449429995020135949113 4326337072496265101961835)
        ·
          refine ⟨6489505608744397652942753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4326337072496265101961835 6489505608744397652942753)
          ·
            refine ⟨4867129206558298239707065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6489505608744397652942753 4867129206558298239707065)
            ·
              refine ⟨3650346904918723679780299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4867129206558298239707065 3650346904918723679780299)
              ·
                refine ⟨5475520357378085519670449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3650346904918723679780299 5475520357378085519670449)
                ·
                  refine ⟨4106640268033564139752837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5475520357378085519670449 4106640268033564139752837)
                  ·
                    refine ⟨769995050256293276203657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4106640268033564139752837 769995050256293276203657)
                    ·
                      refine ⟨577496287692219957152743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 769995050256293276203657 577496287692219957152743)
                      ·
                        rfl

theorem cell23_1124670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 2, 4, 2].length) (baseStart_1124670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1124670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1124670 prefixEnd_1124670 := by exact prefixLift 1124670
  have htrace : WordTrace (prefixWord ++ tailWord_1124670) baseStart_1124670 baseEnd_1124670 := by
    simpa [prefixWord, tailWord_1124670, baseEnd_1124670] using wordTrace_append hprefix tailTrace_1124670
  have hstable : (prefixWord ++ tailWord_1124670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124670).length < 2 ^ (prefixWord ++ tailWord_1124670).sum := by decide
  have hdescent : baseEnd_1124670 < baseStart_1124670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124703 : List Nat := [1, 1, 2, 3, 1, 2, 2, 2, 5, 1, 3]
def baseStart_1124703 : Nat := 118140960795 + 1124703 * 2 ^ 59
def prefixEnd_1124703 : Nat := 4983230072969 + 3 ^ 40 * 1124703 * 2
def baseEnd_1124703 : Nat := 577513232553818328040091

theorem tailTrace_1124703 : CollatzResearch.WordTrace tailWord_1124703 prefixEnd_1124703 577513232553818328040091 := by
  unfold tailWord_1124703
  simp only [CollatzResearch.WordTrace]
  refine ⟨41021288444400589824922763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27347525629600393216615175 41021288444400589824922763)
  ·
    refine ⟨61531932666600884737384145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41021288444400589824922763 61531932666600884737384145)
    ·
      refine ⟨46148949499950663553038109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61531932666600884737384145 46148949499950663553038109)
      ·
        refine ⟨17305856062481498832389291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46148949499950663553038109 17305856062481498832389291)
        ·
          refine ⟨25958784093722248248583937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17305856062481498832389291 25958784093722248248583937)
          ·
            refine ⟨19469088070291686186437953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25958784093722248248583937 19469088070291686186437953)
            ·
              refine ⟨14601816052718764639828465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19469088070291686186437953 14601816052718764639828465)
              ·
                refine ⟨10951362039539073479871349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14601816052718764639828465 10951362039539073479871349)
                ·
                  refine ⟨1026690191206788138737939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10951362039539073479871349 1026690191206788138737939)
                  ·
                    refine ⟨1540035286810182208106909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1026690191206788138737939 1540035286810182208106909)
                    ·
                      refine ⟨577513232553818328040091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1540035286810182208106909 577513232553818328040091)
                      ·
                        rfl

theorem cell23_1124703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 5, 1, 3].length) (baseStart_1124703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1124703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1124703 prefixEnd_1124703 := by exact prefixLift 1124703
  have htrace : WordTrace (prefixWord ++ tailWord_1124703) baseStart_1124703 baseEnd_1124703 := by
    simpa [prefixWord, tailWord_1124703, baseEnd_1124703] using wordTrace_append hprefix tailTrace_1124703
  have hstable : (prefixWord ++ tailWord_1124703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124703).length < 2 ^ (prefixWord ++ tailWord_1124703).sum := by decide
  have hdescent : baseEnd_1124703 < baseStart_1124703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124714 : List Nat := [3, 1, 3, 3, 1, 2, 3, 2, 1, 4]
def baseStart_1124714 : Nat := 118140960795 + 1124714 * 2 ^ 59
def prefixEnd_1124714 : Nat := 4983230072969 + 3 ^ 40 * 1124714 * 2
def baseEnd_1124714 : Nat := 192506293613672595000847

theorem tailTrace_1124714 : CollatzResearch.WordTrace tailWord_1124714 prefixEnd_1124714 192506293613672595000847 := by
  unfold tailWord_1124714
  simp only [CollatzResearch.WordTrace]
  refine ⟨10255422411840184675893299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27347793098240492469048797 10255422411840184675893299)
  ·
    refine ⟨15383133617760277013839949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10255422411840184675893299 15383133617760277013839949)
    ·
      refine ⟨5768675106660103880189981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15383133617760277013839949 5768675106660103880189981)
      ·
        refine ⟨2163253164997538955071243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5768675106660103880189981 2163253164997538955071243)
        ·
          refine ⟨3244879747496308432606865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2163253164997538955071243 3244879747496308432606865)
          ·
            refine ⟨2433659810622231324455149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3244879747496308432606865 2433659810622231324455149)
            ·
              refine ⟨912622428983336746670681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2433659810622231324455149 912622428983336746670681)
              ·
                refine ⟨684466821737502560003011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 912622428983336746670681 684466821737502560003011)
                ·
                  refine ⟨1026700232606253840004517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 684466821737502560003011 1026700232606253840004517)
                  ·
                    refine ⟨192506293613672595000847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1026700232606253840004517 192506293613672595000847)
                    ·
                      rfl

theorem cell23_1124714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 3, 2, 1, 4].length) (baseStart_1124714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1124714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1124714 prefixEnd_1124714 := by exact prefixLift 1124714
  have htrace : WordTrace (prefixWord ++ tailWord_1124714) baseStart_1124714 baseEnd_1124714 := by
    simpa [prefixWord, tailWord_1124714, baseEnd_1124714] using wordTrace_append hprefix tailTrace_1124714
  have hstable : (prefixWord ++ tailWord_1124714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124714).length < 2 ^ (prefixWord ++ tailWord_1124714).sum := by decide
  have hdescent : baseEnd_1124714 < baseStart_1124714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124720 : List Nat := [2, 1, 1, 1, 4, 3, 3, 1, 3, 1, 3]
def baseStart_1124720 : Nat := 118140960795 + 1124720 * 2 ^ 59
def prefixEnd_1124720 : Nat := 4983230072969 + 3 ^ 40 * 1124720 * 2
def baseEnd_1124720 : Nat := 577521961724944761527513

theorem tailTrace_1124720 : CollatzResearch.WordTrace tailWord_1124720 prefixEnd_1124720 577521961724944761527513 := by
  unfold tailWord_1124720
  simp only [CollatzResearch.WordTrace]
  refine ⟨20510954242669500864145807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27347938990226001152194409 20510954242669500864145807)
  ·
    refine ⟨30766431364004251296218711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20510954242669500864145807 30766431364004251296218711)
    ·
      refine ⟨46149647046006376944328067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30766431364004251296218711 46149647046006376944328067)
      ·
        refine ⟨69224470569009565416492101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46149647046006376944328067 69224470569009565416492101)
        ·
          refine ⟨12979588231689293515592269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69224470569009565416492101 12979588231689293515592269)
          ·
            refine ⟨4867345586883485068347101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12979588231689293515592269 4867345586883485068347101)
            ·
              refine ⟨1825254595081306900630163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4867345586883485068347101 1825254595081306900630163)
              ·
                refine ⟨2737881892621960350945245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1825254595081306900630163 2737881892621960350945245)
                ·
                  refine ⟨1026705709733235131604467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2737881892621960350945245 1026705709733235131604467)
                  ·
                    refine ⟨1540058564599852697406701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1026705709733235131604467 1540058564599852697406701)
                    ·
                      refine ⟨577521961724944761527513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1540058564599852697406701 577521961724944761527513)
                      ·
                        rfl

theorem cell23_1124720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 1, 3, 1, 3].length) (baseStart_1124720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1124720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1124720 prefixEnd_1124720 := by exact prefixLift 1124720
  have htrace : WordTrace (prefixWord ++ tailWord_1124720) baseStart_1124720 baseEnd_1124720 := by
    simpa [prefixWord, tailWord_1124720, baseEnd_1124720] using wordTrace_append hprefix tailTrace_1124720
  have hstable : (prefixWord ++ tailWord_1124720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124720).length < 2 ^ (prefixWord ++ tailWord_1124720).sum := by decide
  have hdescent : baseEnd_1124720 < baseStart_1124720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124743 : List Nat := [1, 1, 4, 2, 2, 1, 3, 1, 3, 1, 4]
def baseStart_1124743 : Nat := 118140960795 + 1124743 * 2 ^ 59
def prefixEnd_1124743 : Nat := 4983230072969 + 3 ^ 40 * 1124743 * 2
def baseEnd_1124743 : Nat := 577533771779998171539907

theorem tailTrace_1124743 : CollatzResearch.WordTrace tailWord_1124743 prefixEnd_1124743 577533771779998171539907 := by
  unfold tailWord_1124743
  simp only [CollatzResearch.WordTrace]
  refine ⟨41022747364255676656378883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27348498242837117770919255 41022747364255676656378883)
  ·
    refine ⟨61534121046383514984568325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41022747364255676656378883 61534121046383514984568325)
    ·
      refine ⟨11537647696196909059606561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61534121046383514984568325 11537647696196909059606561)
      ·
        refine ⟨8653235772147681794704921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11537647696196909059606561 8653235772147681794704921)
        ·
          refine ⟨6489926829110761346028691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8653235772147681794704921 6489926829110761346028691)
          ·
            refine ⟨9734890243666142019043037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6489926829110761346028691 9734890243666142019043037)
            ·
              refine ⟨3650583841374803257141139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9734890243666142019043037 3650583841374803257141139)
              ·
                refine ⟨5475875762062204885711709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3650583841374803257141139 5475875762062204885711709)
                ·
                  refine ⟨2053453410773326832141891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5475875762062204885711709 2053453410773326832141891)
                  ·
                    refine ⟨3080180116159990248212837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2053453410773326832141891 3080180116159990248212837)
                    ·
                      refine ⟨577533771779998171539907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3080180116159990248212837 577533771779998171539907)
                      ·
                        rfl

theorem cell23_1124743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_1124743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1124743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1124743 prefixEnd_1124743 := by exact prefixLift 1124743
  have htrace : WordTrace (prefixWord ++ tailWord_1124743) baseStart_1124743 baseEnd_1124743 := by
    simpa [prefixWord, tailWord_1124743, baseEnd_1124743] using wordTrace_append hprefix tailTrace_1124743
  have hstable : (prefixWord ++ tailWord_1124743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124743).length < 2 ^ (prefixWord ++ tailWord_1124743).sum := by decide
  have hdescent : baseEnd_1124743 < baseStart_1124743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124810 : List Nat := [3, 1, 2, 1, 2, 2, 2, 2, 4, 1, 3]
def baseStart_1124810 : Nat := 118140960795 + 1124810 * 2 ^ 59
def prefixEnd_1124810 : Nat := 4983230072969 + 3 ^ 40 * 1124810 * 2
def baseEnd_1124810 : Nat := 577568174983849409402099

theorem tailTrace_1124810 : CollatzResearch.WordTrace tailWord_1124810 prefixEnd_1124810 577568174983849409402099 := by
  unfold tailWord_1124810
  simp only [CollatzResearch.WordTrace]
  refine ⟨10256297763753236774766971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27350127370008631399378589 10256297763753236774766971)
  ·
    refine ⟨15384446645629855162150457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10256297763753236774766971 15384446645629855162150457)
    ·
      refine ⟨11538334984222391371612843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15384446645629855162150457 11538334984222391371612843)
      ·
        refine ⟨17307502476333587057419265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11538334984222391371612843 17307502476333587057419265)
        ·
          refine ⟨12980626857250190293064449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17307502476333587057419265 12980626857250190293064449)
          ·
            refine ⟨9735470142937642719798337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12980626857250190293064449 9735470142937642719798337)
            ·
              refine ⟨7301602607203232039848753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9735470142937642719798337 7301602607203232039848753)
              ·
                refine ⟨5476201955402424029886565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7301602607203232039848753 5476201955402424029886565)
                ·
                  refine ⟨1026787866637954505603731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5476201955402424029886565 1026787866637954505603731)
                  ·
                    refine ⟨1540181799956931758405597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1026787866637954505603731 1540181799956931758405597)
                    ·
                      refine ⟨577568174983849409402099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1540181799956931758405597 577568174983849409402099)
                      ·
                        rfl

theorem cell23_1124810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 4, 1, 3].length) (baseStart_1124810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1124810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1124810 prefixEnd_1124810 := by exact prefixLift 1124810
  have htrace : WordTrace (prefixWord ++ tailWord_1124810) baseStart_1124810 baseEnd_1124810 := by
    simpa [prefixWord, tailWord_1124810, baseEnd_1124810] using wordTrace_append hprefix tailTrace_1124810
  have hstable : (prefixWord ++ tailWord_1124810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124810).length < 2 ^ (prefixWord ++ tailWord_1124810).sum := by decide
  have hdescent : baseEnd_1124810 < baseStart_1124810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124854 : List Nat := [5, 1, 1, 1, 2, 1, 4, 2, 1, 3, 2]
def baseStart_1124854 : Nat := 118140960795 + 1124854 * 2 ^ 59
def prefixEnd_1124854 : Nat := 4983230072969 + 3 ^ 40 * 1124854 * 2
def baseEnd_1124854 : Nat := 577590768132647237251897

theorem tailTrace_1124854 : CollatzResearch.WordTrace tailWord_1124854 prefixEnd_1124854 577590768132647237251897 := by
  unfold tailWord_1124854
  simp only [CollatzResearch.WordTrace]
  refine ⟨2564174741678346413354351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27351197244569028409113077 2564174741678346413354351)
  ·
    refine ⟨3846262112517519620031527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2564174741678346413354351 3846262112517519620031527)
    ·
      refine ⟨5769393168776279430047291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3846262112517519620031527 5769393168776279430047291)
      ·
        refine ⟨8654089753164419145070937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5769393168776279430047291 8654089753164419145070937)
        ·
          refine ⟨6490567314873314358803203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8654089753164419145070937 6490567314873314358803203)
          ·
            refine ⟨9735850972309971538204805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6490567314873314358803203 9735850972309971538204805)
            ·
              refine ⟨1825472057308119663413401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9735850972309971538204805 1825472057308119663413401)
              ·
                refine ⟨1369104042981089747560051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1825472057308119663413401 1369104042981089747560051)
                ·
                  refine ⟨2053656064471634621340077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1369104042981089747560051 2053656064471634621340077)
                  ·
                    refine ⟨770121024176862983002529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2053656064471634621340077 770121024176862983002529)
                    ·
                      refine ⟨577590768132647237251897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 770121024176862983002529 577590768132647237251897)
                      ·
                        rfl

theorem cell23_1124854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 2, 1, 3, 2].length) (baseStart_1124854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1124854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1124854 prefixEnd_1124854 := by exact prefixLift 1124854
  have htrace : WordTrace (prefixWord ++ tailWord_1124854) baseStart_1124854 baseEnd_1124854 := by
    simpa [prefixWord, tailWord_1124854, baseEnd_1124854] using wordTrace_append hprefix tailTrace_1124854
  have hstable : (prefixWord ++ tailWord_1124854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124854).length < 2 ^ (prefixWord ++ tailWord_1124854).sum := by decide
  have hdescent : baseEnd_1124854 < baseStart_1124854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124890 : List Nat := [3, 1, 1, 3, 1, 1, 2, 6, 5]
def baseStart_1124890 : Nat := 118140960795 + 1124890 * 2 ^ 59
def prefixEnd_1124890 : Nat := 4983230072969 + 3 ^ 40 * 1124890 * 2
def baseEnd_1124890 : Nat := 64178805937356566266859

theorem tailTrace_1124890 : CollatzResearch.WordTrace tailWord_1124890 prefixEnd_1124890 64178805937356566266859 := by
  unfold tailWord_1124890
  simp only [CollatzResearch.WordTrace]
  refine ⟨10257027223680780190495031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27352072596482080507986749 10257027223680780190495031)
  ·
    refine ⟨15385540835521170285742547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10257027223680780190495031 15385540835521170285742547)
    ·
      refine ⟨23078311253281755428613821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15385540835521170285742547 23078311253281755428613821)
      ·
        refine ⟨8654366719980658285730183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23078311253281755428613821 8654366719980658285730183)
        ·
          refine ⟨12981550079970987428595275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8654366719980658285730183 12981550079970987428595275)
          ·
            refine ⟨19472325119956481142892913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12981550079970987428595275 19472325119956481142892913)
            ·
              refine ⟨14604243839967360857169685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19472325119956481142892913 14604243839967360857169685)
              ·
                refine ⟨684573929998470040179829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14604243839967360857169685 684573929998470040179829)
                ·
                  refine ⟨64178805937356566266859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 684573929998470040179829 64178805937356566266859)
                  ·
                    rfl

theorem cell23_1124890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 6, 5].length) (baseStart_1124890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1124890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1124890 prefixEnd_1124890 := by exact prefixLift 1124890
  have htrace : WordTrace (prefixWord ++ tailWord_1124890) baseStart_1124890 baseEnd_1124890 := by
    simpa [prefixWord, tailWord_1124890, baseEnd_1124890] using wordTrace_append hprefix tailTrace_1124890
  have hstable : (prefixWord ++ tailWord_1124890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124890).length < 2 ^ (prefixWord ++ tailWord_1124890).sum := by decide
  have hdescent : baseEnd_1124890 < baseStart_1124890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124920 : List Nat := [2, 1, 2, 1, 4, 1, 4, 1, 2, 5]
def baseStart_1124920 : Nat := 118140960795 + 1124920 * 2 ^ 59
def prefixEnd_1124920 : Nat := 4983230072969 + 3 ^ 40 * 1124920 * 2
def baseEnd_1124920 : Nat := 192541552618614659675531

theorem tailTrace_1124920 : CollatzResearch.WordTrace tailWord_1124920 prefixEnd_1124920 192541552618614659675531 := by
  unfold tailWord_1124920
  simp only [CollatzResearch.WordTrace]
  refine ⟨20514601542307217942786107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27352802056409623923714809 20514601542307217942786107)
  ·
    refine ⟨30771902313460826914179161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20514601542307217942786107 30771902313460826914179161)
    ·
      refine ⟨23078926735095620185634371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30771902313460826914179161 23078926735095620185634371)
      ·
        refine ⟨34618390102643430278451557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23078926735095620185634371 34618390102643430278451557)
        ·
          refine ⟨6490948144245643177209667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34618390102643430278451557 6490948144245643177209667)
          ·
            refine ⟨9736422216368464765814501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6490948144245643177209667 9736422216368464765814501)
            ·
              refine ⟨1825579165569087143590219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9736422216368464765814501 1825579165569087143590219)
              ·
                refine ⟨2738368748353630715385329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1825579165569087143590219 2738368748353630715385329)
                ·
                  refine ⟨2053776561265223036538997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2738368748353630715385329 2053776561265223036538997)
                  ·
                    refine ⟨192541552618614659675531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2053776561265223036538997 192541552618614659675531)
                    ·
                      rfl

theorem cell23_1124920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 1, 2, 5].length) (baseStart_1124920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1124920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1124920 prefixEnd_1124920 := by exact prefixLift 1124920
  have htrace : WordTrace (prefixWord ++ tailWord_1124920) baseStart_1124920 baseEnd_1124920 := by
    simpa [prefixWord, tailWord_1124920, baseEnd_1124920] using wordTrace_append hprefix tailTrace_1124920
  have hstable : (prefixWord ++ tailWord_1124920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124920).length < 2 ^ (prefixWord ++ tailWord_1124920).sum := by decide
  have hdescent : baseEnd_1124920 < baseStart_1124920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124940 : List Nat := [2, 2, 1, 3, 1, 2, 1, 4, 2, 1, 4]
def baseStart_1124940 : Nat := 118140960795 + 1124940 * 2 ^ 59
def prefixEnd_1124940 : Nat := 4983230072969 + 3 ^ 40 * 1124940 * 2
def baseEnd_1124940 : Nat := 577634927468933900776501

theorem tailTrace_1124940 : CollatzResearch.WordTrace tailWord_1124940 prefixEnd_1124940 577634927468933900776501 := by
  unfold tailWord_1124940
  simp only [CollatzResearch.WordTrace]
  refine ⟨20514966272270989650650137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27353288363027986200866849 20514966272270989650650137)
  ·
    refine ⟨15386224704203242237987603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20514966272270989650650137 15386224704203242237987603)
    ·
      refine ⟨23079337056304863356981405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15386224704203242237987603 23079337056304863356981405)
      ·
        refine ⟨8654751396114323758868027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23079337056304863356981405 8654751396114323758868027)
        ·
          refine ⟨12982127094171485638302041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8654751396114323758868027 12982127094171485638302041)
          ·
            refine ⟨9736595320628614228726531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12982127094171485638302041 9736595320628614228726531)
            ·
              refine ⟨14604892980942921343089797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9736595320628614228726531 14604892980942921343089797)
              ·
                refine ⟨2738417433926797751829337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14604892980942921343089797 2738417433926797751829337)
                ·
                  refine ⟨2053813075445098313872003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2738417433926797751829337 2053813075445098313872003)
                  ·
                    refine ⟨3080719613167647470808005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2053813075445098313872003 3080719613167647470808005)
                    ·
                      refine ⟨577634927468933900776501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3080719613167647470808005 577634927468933900776501)
                      ·
                        rfl

theorem cell23_1124940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_1124940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1124940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1124940 prefixEnd_1124940 := by exact prefixLift 1124940
  have htrace : WordTrace (prefixWord ++ tailWord_1124940) baseStart_1124940 baseEnd_1124940 := by
    simpa [prefixWord, tailWord_1124940, baseEnd_1124940] using wordTrace_append hprefix tailTrace_1124940
  have hstable : (prefixWord ++ tailWord_1124940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124940).length < 2 ^ (prefixWord ++ tailWord_1124940).sum := by decide
  have hdescent : baseEnd_1124940 < baseStart_1124940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124941 : List Nat := [1, 6, 1, 1, 2, 3, 2, 2, 5]
def baseStart_1124941 : Nat := 118140960795 + 1124941 * 2 ^ 59
def prefixEnd_1124941 : Nat := 4983230072969 + 3 ^ 40 * 1124941 * 2
def baseEnd_1124941 : Nat := 64181715661065377429333

theorem tailTrace_1124941 : CollatzResearch.WordTrace tailWord_1124941 prefixEnd_1124941 64181715661065377429333 := by
  unfold tailWord_1124941
  simp only [CollatzResearch.WordTrace]
  refine ⟨41029969017538356472086677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27353312678358904314724451 41029969017538356472086677)
  ·
    refine ⟨1923279797697110459629063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 41029969017538356472086677 1923279797697110459629063)
    ·
      refine ⟨2884919696545665689443595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1923279797697110459629063 2884919696545665689443595)
      ·
        refine ⟨4327379544818498534165393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2884919696545665689443595 4327379544818498534165393)
        ·
          refine ⟨3245534658613873900624045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4327379544818498534165393 3245534658613873900624045)
          ·
            refine ⟨1217075496980202712734017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3245534658613873900624045 1217075496980202712734017)
            ·
              refine ⟨912806622735152034550513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1217075496980202712734017 912806622735152034550513)
              ·
                refine ⟨684604967051364025912885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 912806622735152034550513 684604967051364025912885)
                ·
                  refine ⟨64181715661065377429333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 684604967051364025912885 64181715661065377429333)
                  ·
                    rfl

theorem cell23_1124941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 2, 2, 5].length) (baseStart_1124941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1124941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1124941 prefixEnd_1124941 := by exact prefixLift 1124941
  have htrace : WordTrace (prefixWord ++ tailWord_1124941) baseStart_1124941 baseEnd_1124941 := by
    simpa [prefixWord, tailWord_1124941, baseEnd_1124941] using wordTrace_append hprefix tailTrace_1124941
  have hstable : (prefixWord ++ tailWord_1124941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124941).length < 2 ^ (prefixWord ++ tailWord_1124941).sum := by decide
  have hdescent : baseEnd_1124941 < baseStart_1124941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124953 : List Nat := [1, 2, 1, 2, 2, 1, 1, 1, 4, 4, 4]
def baseStart_1124953 : Nat := 118140960795 + 1124953 * 2 ^ 59
def prefixEnd_1124953 : Nat := 4983230072969 + 3 ^ 40 * 1124953 * 2
def baseEnd_1124953 : Nat := 577641602717442349913941

theorem tailTrace_1124953 : CollatzResearch.WordTrace tailWord_1124953 prefixEnd_1124953 577641602717442349913941 := by
  unfold tailWord_1124953
  simp only [CollatzResearch.WordTrace]
  refine ⟨41030406693494882521523513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27353604462329921681015675 41030406693494882521523513)
  ·
    refine ⟨30772805020121161891142635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41030406693494882521523513 30772805020121161891142635)
    ·
      refine ⟨46159207530181742836713953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30772805020121161891142635 46159207530181742836713953)
      ·
        refine ⟨34619405647636307127535465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46159207530181742836713953 34619405647636307127535465)
        ·
          refine ⟨25964554235727230345651599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34619405647636307127535465 25964554235727230345651599)
          ·
            refine ⟨38946831353590845518477399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25964554235727230345651599 38946831353590845518477399)
            ·
              refine ⟨58420247030386268277716099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38946831353590845518477399 58420247030386268277716099)
              ·
                refine ⟨87630370545579402416574149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58420247030386268277716099 87630370545579402416574149)
                ·
                  refine ⟨16430694477296137953107653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 87630370545579402416574149 16430694477296137953107653)
                  ·
                    refine ⟨3080755214493025866207685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16430694477296137953107653 3080755214493025866207685)
                    ·
                      refine ⟨577641602717442349913941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3080755214493025866207685 577641602717442349913941)
                      ·
                        rfl

theorem cell23_1124953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 4, 4].length) (baseStart_1124953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1124953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1124953 prefixEnd_1124953 := by exact prefixLift 1124953
  have htrace : WordTrace (prefixWord ++ tailWord_1124953) baseStart_1124953 baseEnd_1124953 := by
    simpa [prefixWord, tailWord_1124953, baseEnd_1124953] using wordTrace_append hprefix tailTrace_1124953
  have hstable : (prefixWord ++ tailWord_1124953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124953).length < 2 ^ (prefixWord ++ tailWord_1124953).sum := by decide
  have hdescent : baseEnd_1124953 < baseStart_1124953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124960 : List Nat := [2, 1, 1, 3, 2, 1, 2, 2, 4, 2, 3]
def baseStart_1124960 : Nat := 118140960795 + 1124960 * 2 ^ 59
def prefixEnd_1124960 : Nat := 4983230072969 + 3 ^ 40 * 1124960 * 2
def baseEnd_1124960 : Nat := 577645197082023822526409

theorem tailTrace_1124960 : CollatzResearch.WordTrace tailWord_1124960 prefixEnd_1124960 577645197082023822526409 := by
  unfold tailWord_1124960
  simp only [CollatzResearch.WordTrace]
  refine ⟨20515331002234761358514167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27353774669646348478018889 20515331002234761358514167)
  ·
    refine ⟨30772996503352142037771251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20515331002234761358514167 30772996503352142037771251)
    ·
      refine ⟨46159494755028213056656877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30772996503352142037771251 46159494755028213056656877)
      ·
        refine ⟨17309810533135579896246329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46159494755028213056656877 17309810533135579896246329)
        ·
          refine ⟨12982357899851684922184747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17309810533135579896246329 12982357899851684922184747)
          ·
            refine ⟨19473536849777527383277121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12982357899851684922184747 19473536849777527383277121)
            ·
              refine ⟨14605152637333145537457841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19473536849777527383277121 14605152637333145537457841)
              ·
                refine ⟨10953864477999859153093381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14605152637333145537457841 10953864477999859153093381)
                ·
                  refine ⟨2053849589624973591205009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10953864477999859153093381 2053849589624973591205009)
                  ·
                    refine ⟨1540387192218730193403757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2053849589624973591205009 1540387192218730193403757)
                    ·
                      refine ⟨577645197082023822526409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1540387192218730193403757 577645197082023822526409)
                      ·
                        rfl

theorem cell23_1124960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 4, 2, 3].length) (baseStart_1124960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1124960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1124960 prefixEnd_1124960 := by exact prefixLift 1124960
  have htrace : WordTrace (prefixWord ++ tailWord_1124960) baseStart_1124960 baseEnd_1124960 := by
    simpa [prefixWord, tailWord_1124960, baseEnd_1124960] using wordTrace_append hprefix tailTrace_1124960
  have hstable : (prefixWord ++ tailWord_1124960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124960).length < 2 ^ (prefixWord ++ tailWord_1124960).sum := by decide
  have hdescent : baseEnd_1124960 < baseStart_1124960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124974 : List Nat := [4, 1, 2, 2, 2, 3, 1, 1, 2, 1, 4]
def baseStart_1124974 : Nat := 118140960795 + 1124974 * 2 ^ 59
def prefixEnd_1124974 : Nat := 4983230072969 + 3 ^ 40 * 1124974 * 2
def baseEnd_1124974 : Nat := 577652385811186767751345

theorem tailTrace_1124974 : CollatzResearch.WordTrace tailWord_1124974 prefixEnd_1124974 577652385811186767751345 := by
  unfold tailWord_1124974
  simp only [CollatzResearch.WordTrace]
  refine ⟨5128896578302350388504747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27354115084279202072025317 5128896578302350388504747)
  ·
    refine ⟨7693344867453525582757121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5128896578302350388504747 7693344867453525582757121)
    ·
      refine ⟨5770008650590144187067841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7693344867453525582757121 5770008650590144187067841)
      ·
        refine ⟨4327506487942608140300881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5770008650590144187067841 4327506487942608140300881)
        ·
          refine ⟨3245629865956956105225661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4327506487942608140300881 3245629865956956105225661)
          ·
            refine ⟨1217111199733858539459623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3245629865956956105225661 1217111199733858539459623)
            ·
              refine ⟨1825666799600787809189435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1217111199733858539459623 1825666799600787809189435)
              ·
                refine ⟨2738500199401181713784153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1825666799600787809189435 2738500199401181713784153)
                ·
                  refine ⟨2053875149550886285338115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2738500199401181713784153 2053875149550886285338115)
                  ·
                    refine ⟨3080812724326329428007173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2053875149550886285338115 3080812724326329428007173)
                    ·
                      refine ⟨577652385811186767751345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3080812724326329428007173 577652385811186767751345)
                      ·
                        rfl

theorem cell23_1124974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_1124974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1124974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1124974 prefixEnd_1124974 := by exact prefixLift 1124974
  have htrace : WordTrace (prefixWord ++ tailWord_1124974) baseStart_1124974 baseEnd_1124974 := by
    simpa [prefixWord, tailWord_1124974, baseEnd_1124974] using wordTrace_append hprefix tailTrace_1124974
  have hstable : (prefixWord ++ tailWord_1124974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124974).length < 2 ^ (prefixWord ++ tailWord_1124974).sum := by decide
  have hdescent : baseEnd_1124974 < baseStart_1124974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124997 : List Nat := [1, 3, 1, 1, 4, 4, 1, 2, 6]
def baseStart_1124997 : Nat := 118140960795 + 1124997 * 2 ^ 59
def prefixEnd_1124997 : Nat := 4983230072969 + 3 ^ 40 * 1124997 * 2
def baseEnd_1124997 : Nat := 64184910651804464195971

theorem tailTrace_1124997 : CollatzResearch.WordTrace tailWord_1124997 prefixEnd_1124997 64184910651804464195971 := by
  unfold tailWord_1124997
  simp only [CollatzResearch.WordTrace]
  refine ⟨41032011505335478036125245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27354674336890318690750163 41032011505335478036125245)
  ·
    refine ⟨15387004314500804263546967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41032011505335478036125245 15387004314500804263546967)
    ·
      refine ⟨23080506471751206395320451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15387004314500804263546967 23080506471751206395320451)
      ·
        refine ⟨34620759707626809592980677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23080506471751206395320451 34620759707626809592980677)
        ·
          refine ⟨6491392445180026798683877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34620759707626809592980677 6491392445180026798683877)
          ·
            refine ⟨1217136083471255024753227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6491392445180026798683877 1217136083471255024753227)
            ·
              refine ⟨1825704125206882537129841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1217136083471255024753227 1825704125206882537129841)
              ·
                refine ⟨1369278093905161902847381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1825704125206882537129841 1369278093905161902847381)
                ·
                  refine ⟨64184910651804464195971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1369278093905161902847381 64184910651804464195971)
                  ·
                    rfl

theorem cell23_1124997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 2, 6].length) (baseStart_1124997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1124997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1124997 prefixEnd_1124997 := by exact prefixLift 1124997
  have htrace : WordTrace (prefixWord ++ tailWord_1124997) baseStart_1124997 baseEnd_1124997 := by
    simpa [prefixWord, tailWord_1124997, baseEnd_1124997] using wordTrace_append hprefix tailTrace_1124997
  have hstable : (prefixWord ++ tailWord_1124997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124997).length < 2 ^ (prefixWord ++ tailWord_1124997).sum := by decide
  have hdescent : baseEnd_1124997 < baseStart_1124997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125003 : List Nat := [1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 7]
def baseStart_1125003 : Nat := 118140960795 + 1125003 * 2 ^ 59
def prefixEnd_1125003 : Nat := 4983230072969 + 3 ^ 40 * 1125003 * 2
def baseEnd_1125003 : Nat := 577667276750167154288711

theorem tailTrace_1125003 : CollatzResearch.WordTrace tailWord_1125003 prefixEnd_1125003 577667276750167154288711 := by
  unfold tailWord_1125003
  simp only [CollatzResearch.WordTrace]
  refine ⟨41032230343313741060843663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27354820228875827373895775 41032230343313741060843663)
  ·
    refine ⟨61548345514970611591265495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41032230343313741060843663 61548345514970611591265495)
    ·
      refine ⟨92322518272455917386898243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61548345514970611591265495 92322518272455917386898243)
      ·
        refine ⟨138483777408683876080347365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92322518272455917386898243 138483777408683876080347365)
        ·
          refine ⟨25965708264128226765065131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 138483777408683876080347365 25965708264128226765065131)
          ·
            refine ⟨38948562396192340147597697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25965708264128226765065131 38948562396192340147597697)
            ·
              refine ⟨29211421797144255110698273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38948562396192340147597697 29211421797144255110698273)
              ·
                refine ⟨21908566347858191333023705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29211421797144255110698273 21908566347858191333023705)
                ·
                  refine ⟨16431424760893643499767779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21908566347858191333023705 16431424760893643499767779)
                  ·
                    refine ⟨24647137141340465249651669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16431424760893643499767779 24647137141340465249651669)
                    ·
                      refine ⟨577667276750167154288711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 24647137141340465249651669 577667276750167154288711)
                      ·
                        rfl

theorem cell23_1125003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 7].length) (baseStart_1125003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1125003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1125003 prefixEnd_1125003 := by exact prefixLift 1125003
  have htrace : WordTrace (prefixWord ++ tailWord_1125003) baseStart_1125003 baseEnd_1125003 := by
    simpa [prefixWord, tailWord_1125003, baseEnd_1125003] using wordTrace_append hprefix tailTrace_1125003
  have hstable : (prefixWord ++ tailWord_1125003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125003).length < 2 ^ (prefixWord ++ tailWord_1125003).sum := by decide
  have hdescent : baseEnd_1125003 < baseStart_1125003 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125070 : List Nat := [4, 1, 1, 1, 3, 2, 1, 10]
def baseStart_1125070 : Nat := 118140960795 + 1125070 * 2 ^ 59
def prefixEnd_1125070 : Nat := 4983230072969 + 3 ^ 40 * 1125070 * 2
def baseEnd_1125070 : Nat := 21396358516815496005589

theorem tailTrace_1125070 : CollatzResearch.WordTrace tailWord_1125070 prefixEnd_1125070 21396358516815496005589 := by
  unfold tailWord_1125070
  simp only [CollatzResearch.WordTrace]
  refine ⟨5129334254258876437941583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27356449356047341002355109 5129334254258876437941583)
  ·
    refine ⟨7694001381388314656912375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5129334254258876437941583 7694001381388314656912375)
    ·
      refine ⟨11541002072082471985368563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7694001381388314656912375 11541002072082471985368563)
      ·
        refine ⟨17311503108123707978052845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11541002072082471985368563 17311503108123707978052845)
        ·
          refine ⟨6491813665546390491769817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17311503108123707978052845 6491813665546390491769817)
          ·
            refine ⟨4868860249159792868827363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6491813665546390491769817 4868860249159792868827363)
            ·
              refine ⟨7303290373739689303241045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4868860249159792868827363 7303290373739689303241045)
              ·
                refine ⟨21396358516815496005589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 7303290373739689303241045 21396358516815496005589)
                ·
                  rfl

theorem cell23_1125070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 10].length) (baseStart_1125070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1125070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1125070 prefixEnd_1125070 := by exact prefixLift 1125070
  have htrace : WordTrace (prefixWord ++ tailWord_1125070) baseStart_1125070 baseEnd_1125070 := by
    simpa [prefixWord, tailWord_1125070, baseEnd_1125070] using wordTrace_append hprefix tailTrace_1125070
  have hstable : (prefixWord ++ tailWord_1125070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125070).length < 2 ^ (prefixWord ++ tailWord_1125070).sum := by decide
  have hdescent : baseEnd_1125070 < baseStart_1125070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125097 : List Nat := [1, 2, 1, 1, 1, 2, 4, 1, 6, 1, 3]
def baseStart_1125097 : Nat := 118140960795 + 1125097 * 2 ^ 59
def prefixEnd_1125097 : Nat := 4983230072969 + 3 ^ 40 * 1125097 * 2
def baseEnd_1125097 : Nat := 577715543931689786513279

theorem tailTrace_1125097 : CollatzResearch.WordTrace tailWord_1125097 prefixEnd_1125097 577715543931689786513279 := by
  unfold tailWord_1125097
  simp only [CollatzResearch.WordTrace]
  refine ⟨41035658804973195114765545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27357105869982130076510363 41035658804973195114765545)
  ·
    refine ⟨30776744103729896336074159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41035658804973195114765545 30776744103729896336074159)
    ·
      refine ⟨46165116155594844504111239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30776744103729896336074159 46165116155594844504111239)
      ·
        refine ⟨69247674233392266756166859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46165116155594844504111239 69247674233392266756166859)
        ·
          refine ⟨103871511350088400134250289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69247674233392266756166859 103871511350088400134250289)
          ·
            refine ⟨77903633512566300100687717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103871511350088400134250289 77903633512566300100687717)
            ·
              refine ⟨14606931283606181268878947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77903633512566300100687717 14606931283606181268878947)
              ·
                refine ⟨21910396925409271903318421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14606931283606181268878947 21910396925409271903318421)
                ·
                  refine ⟨1027049855878559620468051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 21910396925409271903318421 1027049855878559620468051)
                  ·
                    refine ⟨1540574783817839430702077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1027049855878559620468051 1540574783817839430702077)
                    ·
                      refine ⟨577715543931689786513279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1540574783817839430702077 577715543931689786513279)
                      ·
                        rfl

theorem cell23_1125097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 6, 1, 3].length) (baseStart_1125097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1125097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1125097 prefixEnd_1125097 := by exact prefixLift 1125097
  have htrace : WordTrace (prefixWord ++ tailWord_1125097) baseStart_1125097 baseEnd_1125097 := by
    simpa [prefixWord, tailWord_1125097, baseEnd_1125097] using wordTrace_append hprefix tailTrace_1125097
  have hstable : (prefixWord ++ tailWord_1125097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125097).length < 2 ^ (prefixWord ++ tailWord_1125097).sum := by decide
  have hdescent : baseEnd_1125097 < baseStart_1125097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125101 : List Nat := [1, 5, 1, 2, 1, 1, 5, 1, 1, 2, 3]
def baseStart_1125101 : Nat := 118140960795 + 1125101 * 2 ^ 59
def prefixEnd_1125101 : Nat := 4983230072969 + 3 ^ 40 * 1125101 * 2
def baseEnd_1125101 : Nat := 577717597854307770863261

theorem tailTrace_1125101 : CollatzResearch.WordTrace tailWord_1125101 prefixEnd_1125101 577717597854307770863261 := by
  unfold tailWord_1125101
  simp only [CollatzResearch.WordTrace]
  refine ⟨41035804696958703797911157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27357203131305802531940771 41035804696958703797911157)
  ·
    refine ⟨3847106690339878481054171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41035804696958703797911157 3847106690339878481054171)
    ·
      refine ⟨5770660035509817721581257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3847106690339878481054171 5770660035509817721581257)
      ·
        refine ⟨4327995026632363291185943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5770660035509817721581257 4327995026632363291185943)
        ·
          refine ⟨6491992539948544936778915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4327995026632363291185943 6491992539948544936778915)
          ·
            refine ⟨9737988809922817405168373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6491992539948544936778915 9737988809922817405168373)
            ·
              refine ⟨912936450930264131734535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9737988809922817405168373 912936450930264131734535)
              ·
                refine ⟨1369404676395396197601803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 912936450930264131734535 1369404676395396197601803)
                ·
                  refine ⟨2054107014593094296402705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1369404676395396197601803 2054107014593094296402705)
                  ·
                    refine ⟨1540580260944820722302029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2054107014593094296402705 1540580260944820722302029)
                    ·
                      refine ⟨577717597854307770863261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1540580260944820722302029 577717597854307770863261)
                      ·
                        rfl

theorem cell23_1125101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 5, 1, 1, 2, 3].length) (baseStart_1125101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1125101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1125101 prefixEnd_1125101 := by exact prefixLift 1125101
  have htrace : WordTrace (prefixWord ++ tailWord_1125101) baseStart_1125101 baseEnd_1125101 := by
    simpa [prefixWord, tailWord_1125101, baseEnd_1125101] using wordTrace_append hprefix tailTrace_1125101
  have hstable : (prefixWord ++ tailWord_1125101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125101).length < 2 ^ (prefixWord ++ tailWord_1125101).sum := by decide
  have hdescent : baseEnd_1125101 < baseStart_1125101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125109 : List Nat := [1, 3, 6, 1, 1, 2, 2, 2, 1, 1, 3]
def baseStart_1125109 : Nat := 118140960795 + 1125109 * 2 ^ 59
def prefixEnd_1125109 : Nat := 4983230072969 + 3 ^ 40 * 1125109 * 2
def baseEnd_1125109 : Nat := 577721705699543739563225

theorem tailTrace_1125109 : CollatzResearch.WordTrace tailWord_1125109 prefixEnd_1125109 577721705699543739563225 := by
  unfold tailWord_1125109
  simp only [CollatzResearch.WordTrace]
  refine ⟨41036096480929721164202381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27357397653953147442801587 41036096480929721164202381)
  ·
    refine ⟨15388536180348645436575893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41036096480929721164202381 15388536180348645436575893)
    ·
      refine ⟨721337633453842754839495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 15388536180348645436575893 721337633453842754839495)
      ·
        refine ⟨1082006450180764132259243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 721337633453842754839495 1082006450180764132259243)
        ·
          refine ⟨1623009675271146198388865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1082006450180764132259243 1623009675271146198388865)
          ·
            refine ⟨1217257256453359648791649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1623009675271146198388865 1217257256453359648791649)
            ·
              refine ⟨912942942340019736593737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1217257256453359648791649 912942942340019736593737)
              ·
                refine ⟨684707206755014802445303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 912942942340019736593737 684707206755014802445303)
                ·
                  refine ⟨1027060810132522203667955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 684707206755014802445303 1027060810132522203667955)
                  ·
                    refine ⟨1540591215198783305501933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1027060810132522203667955 1540591215198783305501933)
                    ·
                      refine ⟨577721705699543739563225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1540591215198783305501933 577721705699543739563225)
                      ·
                        rfl

theorem cell23_1125109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_1125109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1125109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1125109 prefixEnd_1125109 := by exact prefixLift 1125109
  have htrace : WordTrace (prefixWord ++ tailWord_1125109) baseStart_1125109 baseEnd_1125109 := by
    simpa [prefixWord, tailWord_1125109, baseEnd_1125109] using wordTrace_append hprefix tailTrace_1125109
  have hstable : (prefixWord ++ tailWord_1125109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125109).length < 2 ^ (prefixWord ++ tailWord_1125109).sum := by decide
  have hdescent : baseEnd_1125109 < baseStart_1125109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125114 : List Nat := [3, 1, 1, 1, 1, 3, 3, 4, 2, 1, 3]
def baseStart_1125114 : Nat := 118140960795 + 1125114 * 2 ^ 59
def prefixEnd_1125114 : Nat := 4983230072969 + 3 ^ 40 * 1125114 * 2
def baseEnd_1125114 : Nat := 577724273102816220000701

theorem tailTrace_1125114 : CollatzResearch.WordTrace tailWord_1125114 prefixEnd_1125114 577724273102816220000701 := by
  unfold tailWord_1125114
  simp only [CollatzResearch.WordTrace]
  refine ⟨10259069711477901754533599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27357519230607738012089597 10259069711477901754533599)
  ·
    refine ⟨15388604567216852631800399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10259069711477901754533599 15388604567216852631800399)
    ·
      refine ⟨23082906850825278947700599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15388604567216852631800399 23082906850825278947700599)
      ·
        refine ⟨34624360276237918421550899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23082906850825278947700599 34624360276237918421550899)
        ·
          refine ⟨51936540414356877632326349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34624360276237918421550899 51936540414356877632326349)
          ·
            refine ⟨19476202655383829112122381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51936540414356877632326349 19476202655383829112122381)
            ·
              refine ⟨7303575995768935917045893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19476202655383829112122381 7303575995768935917045893)
              ·
                refine ⟨1369420499206675484446105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7303575995768935917045893 1369420499206675484446105)
                ·
                  refine ⟨1027065374405006613334579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1369420499206675484446105 1027065374405006613334579)
                  ·
                    refine ⟨1540598061607509920001869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1027065374405006613334579 1540598061607509920001869)
                    ·
                      refine ⟨577724273102816220000701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1540598061607509920001869 577724273102816220000701)
                      ·
                        rfl

theorem cell23_1125114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 4, 2, 1, 3].length) (baseStart_1125114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1125114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1125114 prefixEnd_1125114 := by exact prefixLift 1125114
  have htrace : WordTrace (prefixWord ++ tailWord_1125114) baseStart_1125114 baseEnd_1125114 := by
    simpa [prefixWord, tailWord_1125114, baseEnd_1125114] using wordTrace_append hprefix tailTrace_1125114
  have hstable : (prefixWord ++ tailWord_1125114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125114).length < 2 ^ (prefixWord ++ tailWord_1125114).sum := by decide
  have hdescent : baseEnd_1125114 < baseStart_1125114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125124 : List Nat := [2, 3, 2, 2, 1, 1, 1, 1, 5, 3, 2]
def baseStart_1125124 : Nat := 118140960795 + 1125124 * 2 ^ 59
def prefixEnd_1125124 : Nat := 4983230072969 + 3 ^ 40 * 1125124 * 2
def baseEnd_1125124 : Nat := 577729407909361180875655

theorem tailTrace_1125124 : CollatzResearch.WordTrace tailWord_1125124 prefixEnd_1125124 577729407909361180875655 := by
  unfold tailWord_1125124
  simp only [CollatzResearch.WordTrace]
  refine ⟨20518321787937689362999213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27357762383916919150665617 20518321787937689362999213)
  ·
    refine ⟨7694370670476633511124705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20518321787937689362999213 7694370670476633511124705)
    ·
      refine ⟨5770778002857475133343529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7694370670476633511124705 5770778002857475133343529)
      ·
        refine ⟨4328083502143106350007647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5770778002857475133343529 4328083502143106350007647)
        ·
          refine ⟨6492125253214659525011471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4328083502143106350007647 6492125253214659525011471)
          ·
            refine ⟨9738187879821989287517207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6492125253214659525011471 9738187879821989287517207)
            ·
              refine ⟨14607281819732983931275811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9738187879821989287517207 14607281819732983931275811)
              ·
                refine ⟨21910922729599475896913717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14607281819732983931275811 21910922729599475896913717)
                ·
                  refine ⟨2054149005899950865335661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21910922729599475896913717 2054149005899950865335661)
                  ·
                    refine ⟨770305877212481574500873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2054149005899950865335661 770305877212481574500873)
                    ·
                      refine ⟨577729407909361180875655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 770305877212481574500873 577729407909361180875655)
                      ·
                        rfl

theorem cell23_1125124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 5, 3, 2].length) (baseStart_1125124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1125124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1125124 prefixEnd_1125124 := by exact prefixLift 1125124
  have htrace : WordTrace (prefixWord ++ tailWord_1125124) baseStart_1125124 baseEnd_1125124 := by
    simpa [prefixWord, tailWord_1125124, baseEnd_1125124] using wordTrace_append hprefix tailTrace_1125124
  have hstable : (prefixWord ++ tailWord_1125124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125124).length < 2 ^ (prefixWord ++ tailWord_1125124).sum := by decide
  have hdescent : baseEnd_1125124 < baseStart_1125124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125171 : List Nat := [1, 1, 1, 2, 6, 2, 1, 1, 4, 2, 2]
def baseStart_1125171 : Nat := 118140960795 + 1125171 * 2 ^ 59
def prefixEnd_1125171 : Nat := 4983230072969 + 3 ^ 40 * 1125171 * 2
def baseEnd_1125171 : Nat := 577753541500122496987939

theorem tailTrace_1125171 : CollatzResearch.WordTrace tailWord_1125171 prefixEnd_1125171 577753541500122496987939 := by
  unfold tailWord_1125171
  simp only [CollatzResearch.WordTrace]
  refine ⟨41038357806705105752959367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27358905204470070501972911 41038357806705105752959367)
  ·
    refine ⟨61557536710057658629439051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41038357806705105752959367 61557536710057658629439051)
    ·
      refine ⟨92336305065086487944158577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61557536710057658629439051 92336305065086487944158577)
      ·
        refine ⟨69252228798814865958118933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92336305065086487944158577 69252228798814865958118933)
        ·
          refine ⟨3246198224944446841786825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 69252228798814865958118933 3246198224944446841786825)
          ·
            refine ⟨2434648668708335131340119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3246198224944446841786825 2434648668708335131340119)
            ·
              refine ⟨3651973003062502697010179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2434648668708335131340119 3651973003062502697010179)
              ·
                refine ⟨5477959504593754045515269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3651973003062502697010179 5477959504593754045515269)
                ·
                  refine ⟨1027117407111328883534113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5477959504593754045515269 1027117407111328883534113)
                  ·
                    refine ⟨770338055333496662650585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1027117407111328883534113 770338055333496662650585)
                    ·
                      refine ⟨577753541500122496987939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 770338055333496662650585 577753541500122496987939)
                      ·
                        rfl

theorem cell23_1125171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 4, 2, 2].length) (baseStart_1125171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1125171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1125171 prefixEnd_1125171 := by exact prefixLift 1125171
  have htrace : WordTrace (prefixWord ++ tailWord_1125171) baseStart_1125171 baseEnd_1125171 := by
    simpa [prefixWord, tailWord_1125171, baseEnd_1125171] using wordTrace_append hprefix tailTrace_1125171
  have hstable : (prefixWord ++ tailWord_1125171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125171).length < 2 ^ (prefixWord ++ tailWord_1125171).sum := by decide
  have hdescent : baseEnd_1125171 < baseStart_1125171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125187 : List Nat := [1, 1, 1, 3, 1, 4, 1, 3, 2, 3, 3]
def baseStart_1125187 : Nat := 118140960795 + 1125187 * 2 ^ 59
def prefixEnd_1125187 : Nat := 4983230072969 + 3 ^ 40 * 1125187 * 2
def baseEnd_1125187 : Nat := 577761757190594434387865

theorem tailTrace_1125187 : CollatzResearch.WordTrace tailWord_1125187 prefixEnd_1125187 577761757190594434387865 := by
  unfold tailWord_1125187
  simp only [CollatzResearch.WordTrace]
  refine ⟨41038941374647140485541815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27359294249764760323694543 41038941374647140485541815)
  ·
    refine ⟨61558412061970710728312723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41038941374647140485541815 61558412061970710728312723)
    ·
      refine ⟨92337618092956066092469085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61558412061970710728312723 92337618092956066092469085)
      ·
        refine ⟨34626606784858524784675907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92337618092956066092469085 34626606784858524784675907)
        ·
          refine ⟨51939910177287787177013861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34626606784858524784675907 51939910177287787177013861)
          ·
            refine ⟨9738733158241460095690099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51939910177287787177013861 9738733158241460095690099)
            ·
              refine ⟨14608099737362190143535149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9738733158241460095690099 14608099737362190143535149)
              ·
                refine ⟨5478037401510821303825681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14608099737362190143535149 5478037401510821303825681)
                ·
                  refine ⟨4108528051133115977869261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5478037401510821303825681 4108528051133115977869261)
                  ·
                    refine ⟨1540698019174918491700973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4108528051133115977869261 1540698019174918491700973)
                    ·
                      refine ⟨577761757190594434387865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1540698019174918491700973 577761757190594434387865)
                      ·
                        rfl

theorem cell23_1125187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 2, 3, 3].length) (baseStart_1125187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1125187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1125187 prefixEnd_1125187 := by exact prefixLift 1125187
  have htrace : WordTrace (prefixWord ++ tailWord_1125187) baseStart_1125187 baseEnd_1125187 := by
    simpa [prefixWord, tailWord_1125187, baseEnd_1125187] using wordTrace_append hprefix tailTrace_1125187
  have hstable : (prefixWord ++ tailWord_1125187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125187).length < 2 ^ (prefixWord ++ tailWord_1125187).sum := by decide
  have hdescent : baseEnd_1125187 < baseStart_1125187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125207 : List Nat := [1, 1, 3, 2, 4, 1, 2, 1, 1, 7]
def baseStart_1125207 : Nat := 118140960795 + 1125207 * 2 ^ 59
def prefixEnd_1125207 : Nat := 4983230072969 + 3 ^ 40 * 1125207 * 2
def baseEnd_1125207 : Nat := 192590675601228118712591

theorem tailTrace_1125207 : CollatzResearch.WordTrace tailWord_1125207 prefixEnd_1125207 192590675601228118712591 := by
  unfold tailWord_1125207
  simp only [CollatzResearch.WordTrace]
  refine ⟨41039670834574683901269875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27359780556383122600846583 41039670834574683901269875)
  ·
    refine ⟨61559506251862025851904813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41039670834574683901269875 61559506251862025851904813)
    ·
      refine ⟨23084814844448259694464305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61559506251862025851904813 23084814844448259694464305)
      ·
        refine ⟨17313611133336194770848229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23084814844448259694464305 17313611133336194770848229)
        ·
          refine ⟨3246302087500536519534043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17313611133336194770848229 3246302087500536519534043)
          ·
            refine ⟨4869453131250804779301065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3246302087500536519534043 4869453131250804779301065)
            ·
              refine ⟨3652089848438103584475799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4869453131250804779301065 3652089848438103584475799)
              ·
                refine ⟨5478134772657155376713699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3652089848438103584475799 5478134772657155376713699)
                ·
                  refine ⟨8217202158985733065070549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5478134772657155376713699 8217202158985733065070549)
                  ·
                    refine ⟨192590675601228118712591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8217202158985733065070549 192590675601228118712591)
                    ·
                      rfl

theorem cell23_1125207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 7].length) (baseStart_1125207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1125207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1125207 prefixEnd_1125207 := by exact prefixLift 1125207
  have htrace : WordTrace (prefixWord ++ tailWord_1125207) baseStart_1125207 baseEnd_1125207 := by
    simpa [prefixWord, tailWord_1125207, baseEnd_1125207] using wordTrace_append hprefix tailTrace_1125207
  have hstable : (prefixWord ++ tailWord_1125207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125207).length < 2 ^ (prefixWord ++ tailWord_1125207).sum := by decide
  have hdescent : baseEnd_1125207 < baseStart_1125207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125224 : List Nat := [2, 1, 4, 2, 1, 3, 1, 2, 2, 5]
def baseStart_1125224 : Nat := 118140960795 + 1125224 * 2 ^ 59
def prefixEnd_1125224 : Nat := 4983230072969 + 3 ^ 40 * 1125224 * 2
def baseEnd_1125224 : Nat := 192593585324936929875065

theorem tailTrace_1125224 : CollatzResearch.WordTrace tailWord_1125224 prefixEnd_1125224 192593585324936929875065 := by
  unfold tailWord_1125224
  simp only [CollatzResearch.WordTrace]
  refine ⟨20520145437756547902319363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27360193917008730536425817 20520145437756547902319363)
  ·
    refine ⟨30780218156634821853479045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20520145437756547902319363 30780218156634821853479045)
    ·
      refine ⟨5771290904369029097527321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30780218156634821853479045 5771290904369029097527321)
      ·
        refine ⟨4328468178276771823145491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5771290904369029097527321 4328468178276771823145491)
        ·
          refine ⟨6492702267415157734718237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4328468178276771823145491 6492702267415157734718237)
          ·
            refine ⟨2434763350280684150519339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6492702267415157734718237 2434763350280684150519339)
            ·
              refine ⟨3652145025421026225779009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2434763350280684150519339 3652145025421026225779009)
              ·
                refine ⟨2739108769065769669334257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3652145025421026225779009 2739108769065769669334257)
                ·
                  refine ⟨2054331576799327252000693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2739108769065769669334257 2054331576799327252000693)
                  ·
                    refine ⟨192593585324936929875065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2054331576799327252000693 192593585324936929875065)
                    ·
                      rfl

theorem cell23_1125224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 2, 2, 5].length) (baseStart_1125224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1125224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1125224 prefixEnd_1125224 := by exact prefixLift 1125224
  have htrace : WordTrace (prefixWord ++ tailWord_1125224) baseStart_1125224 baseEnd_1125224 := by
    simpa [prefixWord, tailWord_1125224, baseEnd_1125224] using wordTrace_append hprefix tailTrace_1125224
  have hstable : (prefixWord ++ tailWord_1125224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125224).length < 2 ^ (prefixWord ++ tailWord_1125224).sum := by decide
  have hdescent : baseEnd_1125224 < baseStart_1125224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
