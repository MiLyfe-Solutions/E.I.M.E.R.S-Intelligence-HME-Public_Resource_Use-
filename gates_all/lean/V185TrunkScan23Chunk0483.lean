import V185TrunkScan23Chunk0482

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2857296 : List Nat := [2, 1, 1, 1, 1, 6, 1, 5, 1, 4]
def baseStart_2857296 : Nat := 118140960795 + 2857296 * 2 ^ 59
def prefixEnd_2857296 : Nat := 4983230072969 + 3 ^ 40 * 2857296 * 2
def baseEnd_2857296 : Nat := 489055406723052683319847

theorem tailTrace_2857296 : CollatzResearch.WordTrace tailWord_2857296 prefixEnd_2857296 489055406723052683319847 := by
  unfold tailWord_2857296
  simp only [CollatzResearch.WordTrace]
  refine ⟨52107073328256027075627871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69476097771008036100837161 52107073328256027075627871)
  ·
    refine ⟨78160609992384040613441807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52107073328256027075627871 78160609992384040613441807)
    ·
      refine ⟨117240914988576060920162711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78160609992384040613441807 117240914988576060920162711)
      ·
        refine ⟨175861372482864091380244067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117240914988576060920162711 175861372482864091380244067)
        ·
          refine ⟨263792058724296137070366101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175861372482864091380244067 263792058724296137070366101)
          ·
            refine ⟨12365252752701381425173411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 263792058724296137070366101 12365252752701381425173411)
            ·
              refine ⟨18547879129052072137760117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12365252752701381425173411 18547879129052072137760117)
              ·
                refine ⟨1738863668348631762915011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18547879129052072137760117 1738863668348631762915011)
                ·
                  refine ⟨2608295502522947644372517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1738863668348631762915011 2608295502522947644372517)
                  ·
                    refine ⟨489055406723052683319847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2608295502522947644372517 489055406723052683319847)
                    ·
                      rfl

theorem cell23_2857296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 5, 1, 4].length) (baseStart_2857296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2857296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2857296 prefixEnd_2857296 := by exact prefixLift 2857296
  have htrace : WordTrace (prefixWord ++ tailWord_2857296) baseStart_2857296 baseEnd_2857296 := by
    simpa [prefixWord, tailWord_2857296, baseEnd_2857296] using wordTrace_append hprefix tailTrace_2857296
  have hstable : (prefixWord ++ tailWord_2857296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857296).length < 2 ^ (prefixWord ++ tailWord_2857296).sum := by decide
  have hdescent : baseEnd_2857296 < baseStart_2857296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857339 : List Nat := [1, 1, 1, 1, 1, 7, 1, 4, 1, 5]
def baseStart_2857339 : Nat := 118140960795 + 2857339 * 2 ^ 59
def prefixEnd_2857339 : Nat := 4983230072969 + 3 ^ 40 * 2857339 * 2
def baseEnd_2857339 : Nat := 489062766612433793907281

theorem tailTrace_2857339 : CollatzResearch.WordTrace tailWord_2857339 prefixEnd_2857339 489062766612433793907281 := by
  unfold tailWord_2857339
  simp only [CollatzResearch.WordTrace]
  refine ⟨104215714995356272495071071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69477143330237514996714047 104215714995356272495071071)
  ·
    refine ⟨156323572493034408742606607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104215714995356272495071071 156323572493034408742606607)
    ·
      refine ⟨234485358739551613113909911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156323572493034408742606607 234485358739551613113909911)
      ·
        refine ⟨351728038109327419670864867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234485358739551613113909911 351728038109327419670864867)
        ·
          refine ⟨527592057163991129506297301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 351728038109327419670864867 527592057163991129506297301)
          ·
            refine ⟨12365438839781042097803843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 527592057163991129506297301 12365438839781042097803843)
            ·
              refine ⟨18548158259671563146705765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12365438839781042097803843 18548158259671563146705765)
              ·
                refine ⟨3477779673688418090007331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18548158259671563146705765 3477779673688418090007331)
                ·
                  refine ⟨5216669510532627135010997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3477779673688418090007331 5216669510532627135010997)
                  ·
                    refine ⟨489062766612433793907281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5216669510532627135010997 489062766612433793907281)
                    ·
                      rfl

theorem cell23_2857339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 4, 1, 5].length) (baseStart_2857339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2857339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2857339 prefixEnd_2857339 := by exact prefixLift 2857339
  have htrace : WordTrace (prefixWord ++ tailWord_2857339) baseStart_2857339 baseEnd_2857339 := by
    simpa [prefixWord, tailWord_2857339, baseEnd_2857339] using wordTrace_append hprefix tailTrace_2857339
  have hstable : (prefixWord ++ tailWord_2857339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857339).length < 2 ^ (prefixWord ++ tailWord_2857339).sum := by decide
  have hdescent : baseEnd_2857339 < baseStart_2857339 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857369 : List Nat := [1, 2, 1, 2, 1, 4, 1, 3, 4, 4]
def baseStart_2857369 : Nat := 118140960795 + 2857369 * 2 ^ 59
def prefixEnd_2857369 : Nat := 4983230072969 + 3 ^ 40 * 2857369 * 2
def baseEnd_2857369 : Nat := 489067901418978754782235

theorem tailTrace_2857369 : CollatzResearch.WordTrace tailWord_2857369 prefixEnd_2857369 489067901418978754782235 := by
  unfold tailWord_2857369
  simp only [CollatzResearch.WordTrace]
  refine ⟨104216809185247587618663161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69477872790165058412442107 104216809185247587618663161)
  ·
    refine ⟨78162606888935690713997371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104216809185247587618663161 78162606888935690713997371)
    ·
      refine ⟨117243910333403536070996057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78162606888935690713997371 117243910333403536070996057)
      ·
        refine ⟨87932932750052652053247043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117243910333403536070996057 87932932750052652053247043)
        ·
          refine ⟨131899399125078978079870565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87932932750052652053247043 131899399125078978079870565)
          ·
            refine ⟨24731137335952308389975731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 131899399125078978079870565 24731137335952308389975731)
            ·
              refine ⟨37096706003928462584963597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24731137335952308389975731 37096706003928462584963597)
              ·
                refine ⟨13911264751473173469361349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37096706003928462584963597 13911264751473173469361349)
                ·
                  refine ⟨2608362140901220025505253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13911264751473173469361349 2608362140901220025505253)
                  ·
                    refine ⟨489067901418978754782235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2608362140901220025505253 489067901418978754782235)
                    ·
                      rfl

theorem cell23_2857369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 4, 4].length) (baseStart_2857369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2857369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2857369 prefixEnd_2857369 := by exact prefixLift 2857369
  have htrace : WordTrace (prefixWord ++ tailWord_2857369) baseStart_2857369 baseEnd_2857369 := by
    simpa [prefixWord, tailWord_2857369, baseEnd_2857369] using wordTrace_append hprefix tailTrace_2857369
  have hstable : (prefixWord ++ tailWord_2857369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857369).length < 2 ^ (prefixWord ++ tailWord_2857369).sum := by decide
  have hdescent : baseEnd_2857369 < baseStart_2857369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857379 : List Nat := [1, 1, 1, 4, 1, 4, 2, 2, 1, 1, 5]
def baseStart_2857379 : Nat := 118140960795 + 2857379 * 2 ^ 59
def prefixEnd_2857379 : Nat := 4983230072969 + 3 ^ 40 * 2857379 * 2
def baseEnd_2857379 : Nat := 1467208839063481225221659

theorem tailTrace_2857379 : CollatzResearch.WordTrace tailWord_2857379 prefixEnd_2857379 1467208839063481225221659 := by
  unfold tailWord_2857379
  simp only [CollatzResearch.WordTrace]
  refine ⟨104217173915211359326527191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69478115943474239551018127 104217173915211359326527191)
  ·
    refine ⟨156325760872817038989790787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104217173915211359326527191 156325760872817038989790787)
    ·
      refine ⟨234488641309225558484686181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156325760872817038989790787 234488641309225558484686181)
      ·
        refine ⟨43966620245479792215878659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 234488641309225558484686181 43966620245479792215878659)
        ·
          refine ⟨65949930368219688323817989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43966620245479792215878659 65949930368219688323817989)
          ·
            refine ⟨12365611944041191560715873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65949930368219688323817989 12365611944041191560715873)
            ·
              refine ⟨9274208958030893670536905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12365611944041191560715873 9274208958030893670536905)
              ·
                refine ⟨6955656718523170252902679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9274208958030893670536905 6955656718523170252902679)
                ·
                  refine ⟨10433485077784755379354019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6955656718523170252902679 10433485077784755379354019)
                  ·
                    refine ⟨15650227616677133069031029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10433485077784755379354019 15650227616677133069031029)
                    ·
                      refine ⟨1467208839063481225221659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15650227616677133069031029 1467208839063481225221659)
                      ·
                        rfl

theorem cell23_2857379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 2, 1, 1, 5].length) (baseStart_2857379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2857379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2857379 prefixEnd_2857379 := by exact prefixLift 2857379
  have htrace : WordTrace (prefixWord ++ tailWord_2857379) baseStart_2857379 baseEnd_2857379 := by
    simpa [prefixWord, tailWord_2857379, baseEnd_2857379] using wordTrace_append hprefix tailTrace_2857379
  have hstable : (prefixWord ++ tailWord_2857379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857379).length < 2 ^ (prefixWord ++ tailWord_2857379).sum := by decide
  have hdescent : baseEnd_2857379 < baseStart_2857379 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857393 : List Nat := [1, 2, 2, 4, 1, 4, 1, 2, 1, 1, 4]
def baseStart_2857393 : Nat := 118140960795 + 2857393 * 2 ^ 59
def prefixEnd_2857393 : Nat := 4983230072969 + 3 ^ 40 * 2857393 * 2
def baseEnd_2857393 : Nat := 1467216027792644170446595

theorem tailTrace_2857393 : CollatzResearch.WordTrace tailWord_2857393 prefixEnd_2857393 1467216027792644170446595 := by
  unfold tailWord_2857393
  simp only [CollatzResearch.WordTrace]
  refine ⟨104217684537160639717536833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69478456358107093145024555 104217684537160639717536833)
  ·
    refine ⟨78163263402870479788152625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104217684537160639717536833 78163263402870479788152625)
    ·
      refine ⟨58622447552152859841114469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78163263402870479788152625 58622447552152859841114469)
      ·
        refine ⟨10991708916028661220208963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58622447552152859841114469 10991708916028661220208963)
        ·
          refine ⟨16487563374042991830313445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10991708916028661220208963 16487563374042991830313445)
          ·
            refine ⟨3091418132633060968183771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16487563374042991830313445 3091418132633060968183771)
            ·
              refine ⟨4637127198949591452275657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3091418132633060968183771 4637127198949591452275657)
              ·
                refine ⟨3477845399212193589206743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4637127198949591452275657 3477845399212193589206743)
                ·
                  refine ⟨5216768098818290383810115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3477845399212193589206743 5216768098818290383810115)
                  ·
                    refine ⟨7825152148227435575715173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5216768098818290383810115 7825152148227435575715173)
                    ·
                      refine ⟨1467216027792644170446595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7825152148227435575715173 1467216027792644170446595)
                      ·
                        rfl

theorem cell23_2857393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_2857393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2857393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2857393 prefixEnd_2857393 := by exact prefixLift 2857393
  have htrace : WordTrace (prefixWord ++ tailWord_2857393) baseStart_2857393 baseEnd_2857393 := by
    simpa [prefixWord, tailWord_2857393, baseEnd_2857393] using wordTrace_append hprefix tailTrace_2857393
  have hstable : (prefixWord ++ tailWord_2857393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857393).length < 2 ^ (prefixWord ++ tailWord_2857393).sum := by decide
  have hdescent : baseEnd_2857393 < baseStart_2857393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857429 : List Nat := [1, 3, 2, 3, 1, 2, 1, 1, 2, 7]
def baseStart_2857429 : Nat := 118140960795 + 2857429 * 2 ^ 59
def prefixEnd_2857429 : Nat := 4983230072969 + 3 ^ 40 * 2857429 * 2
def baseEnd_2857429 : Nat := 489078171032068676532143

theorem tailTrace_2857429 : CollatzResearch.WordTrace tailWord_2857429 prefixEnd_2857429 489078171032068676532143 := by
  unfold tailWord_2857429
  simp only [CollatzResearch.WordTrace]
  refine ⟨104218997565030217865847341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69479331710020145243898227 104218997565030217865847341)
  ·
    refine ⟨39082124086886331699692753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104218997565030217865847341 39082124086886331699692753)
    ·
      refine ⟨29311593065164748774769565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39082124086886331699692753 29311593065164748774769565)
      ·
        refine ⟨10991847399436780790538587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29311593065164748774769565 10991847399436780790538587)
        ·
          refine ⟨16487771099155171185807881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10991847399436780790538587 16487771099155171185807881)
          ·
            refine ⟨12365828324366378389355911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16487771099155171185807881 12365828324366378389355911)
            ·
              refine ⟨18548742486549567584033867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12365828324366378389355911 18548742486549567584033867)
              ·
                refine ⟨27823113729824351376050801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18548742486549567584033867 27823113729824351376050801)
                ·
                  refine ⟨20867335297368263532038101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27823113729824351376050801 20867335297368263532038101)
                  ·
                    refine ⟨489078171032068676532143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20867335297368263532038101 489078171032068676532143)
                    ·
                      rfl

theorem cell23_2857429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 7].length) (baseStart_2857429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2857429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2857429 prefixEnd_2857429 := by exact prefixLift 2857429
  have htrace : WordTrace (prefixWord ++ tailWord_2857429) baseStart_2857429 baseEnd_2857429 := by
    simpa [prefixWord, tailWord_2857429, baseEnd_2857429] using wordTrace_append hprefix tailTrace_2857429
  have hstable : (prefixWord ++ tailWord_2857429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857429).length < 2 ^ (prefixWord ++ tailWord_2857429).sum := by decide
  have hdescent : baseEnd_2857429 < baseStart_2857429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857443 : List Nat := [1, 1, 1, 6, 3, 1, 2, 1, 1, 3, 3]
def baseStart_2857443 : Nat := 118140960795 + 2857443 * 2 ^ 59
def prefixEnd_2857443 : Nat := 4983230072969 + 3 ^ 40 * 2857443 * 2
def baseEnd_2857443 : Nat := 1467241701825368974821365

theorem tailTrace_2857443 : CollatzResearch.WordTrace tailWord_2857443 prefixEnd_2857443 1467241701825368974821365 := by
  unfold tailWord_2857443
  simp only [CollatzResearch.WordTrace]
  refine ⟨104219508186979498256856983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69479672124652998837904655 104219508186979498256856983)
  ·
    refine ⟨156329262280469247385285475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104219508186979498256856983 156329262280469247385285475)
    ·
      refine ⟨234493893420703871077928213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156329262280469247385285475 234493893420703871077928213)
      ·
        refine ⟨10991901254095493956777885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 234493893420703871077928213 10991901254095493956777885)
        ·
          refine ⟨4121962970285810233791707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10991901254095493956777885 4121962970285810233791707)
          ·
            refine ⟨6182944455428715350687561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4121962970285810233791707 6182944455428715350687561)
            ·
              refine ⟨4637208341571536513015671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6182944455428715350687561 4637208341571536513015671)
              ·
                refine ⟨6955812512357304769523507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4637208341571536513015671 6955812512357304769523507)
                ·
                  refine ⟨10433718768535957154285261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6955812512357304769523507 10433718768535957154285261)
                  ·
                    refine ⟨3912644538200983932856973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10433718768535957154285261 3912644538200983932856973)
                    ·
                      refine ⟨1467241701825368974821365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3912644538200983932856973 1467241701825368974821365)
                      ·
                        rfl

theorem cell23_2857443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_2857443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2857443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2857443 prefixEnd_2857443 := by exact prefixLift 2857443
  have htrace : WordTrace (prefixWord ++ tailWord_2857443) baseStart_2857443 baseEnd_2857443 := by
    simpa [prefixWord, tailWord_2857443, baseEnd_2857443] using wordTrace_append hprefix tailTrace_2857443
  have hstable : (prefixWord ++ tailWord_2857443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857443).length < 2 ^ (prefixWord ++ tailWord_2857443).sum := by decide
  have hdescent : baseEnd_2857443 < baseStart_2857443 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857466 : List Nat := [3, 1, 1, 1, 1, 2, 2, 3, 3, 4, 2]
def baseStart_2857466 : Nat := 118140960795 + 2857466 * 2 ^ 59
def prefixEnd_2857466 : Nat := 4983230072969 + 3 ^ 40 * 2857466 * 2
def baseEnd_2857466 : Nat := 1467253511880422384833759

theorem tailTrace_2857466 : CollatzResearch.WordTrace tailWord_2857466 prefixEnd_2857466 1467253511880422384833759 := by
  unfold tailWord_2857466
  simp only [CollatzResearch.WordTrace]
  refine ⟨26055086766474043296236063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69480231377264115456629501 26055086766474043296236063)
  ·
    refine ⟨39082630149711064944354095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26055086766474043296236063 39082630149711064944354095)
    ·
      refine ⟨58623945224566597416531143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39082630149711064944354095 58623945224566597416531143)
      ·
        refine ⟨87935917836849896124796715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58623945224566597416531143 87935917836849896124796715)
        ·
          refine ⟨131903876755274844187195073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87935917836849896124796715 131903876755274844187195073)
          ·
            refine ⟨98927907566456133140396305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131903876755274844187195073 98927907566456133140396305)
            ·
              refine ⟨74195930674842099855297229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98927907566456133140396305 74195930674842099855297229)
              ·
                refine ⟨27823474003065787445736461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74195930674842099855297229 27823474003065787445736461)
                ·
                  refine ⟨10433802751149670292151173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27823474003065787445736461 10433802751149670292151173)
                  ·
                    refine ⟨1956338015840563179778345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10433802751149670292151173 1956338015840563179778345)
                    ·
                      refine ⟨1467253511880422384833759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1956338015840563179778345 1467253511880422384833759)
                      ·
                        rfl

theorem cell23_2857466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 3, 4, 2].length) (baseStart_2857466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2857466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2857466 prefixEnd_2857466 := by exact prefixLift 2857466
  have htrace : WordTrace (prefixWord ++ tailWord_2857466) baseStart_2857466 baseEnd_2857466 := by
    simpa [prefixWord, tailWord_2857466, baseEnd_2857466] using wordTrace_append hprefix tailTrace_2857466
  have hstable : (prefixWord ++ tailWord_2857466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857466).length < 2 ^ (prefixWord ++ tailWord_2857466).sum := by decide
  have hdescent : baseEnd_2857466 < baseStart_2857466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857469 : List Nat := [1, 4, 1, 1, 1, 3, 2, 1, 1, 3, 5]
def baseStart_2857469 : Nat := 118140960795 + 2857469 * 2 ^ 59
def prefixEnd_2857469 : Nat := 4983230072969 + 3 ^ 40 * 2857469 * 2
def baseEnd_2857469 : Nat := 1467255052322385873096245

theorem tailTrace_2857469 : CollatzResearch.WordTrace tailWord_2857469 prefixEnd_2857469 1467255052322385873096245 := by
  unfold tailWord_2857469
  simp only [CollatzResearch.WordTrace]
  refine ⟨104220456484885304697303461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69480304323256869798202307 104220456484885304697303461)
  ·
    refine ⟨19541335590915994630744399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104220456484885304697303461 19541335590915994630744399)
    ·
      refine ⟨29312003386373991946116599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19541335590915994630744399 29312003386373991946116599)
      ·
        refine ⟨43968005079560987919174899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29312003386373991946116599 43968005079560987919174899)
        ·
          refine ⟨65952007619341481878762349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43968005079560987919174899 65952007619341481878762349)
          ·
            refine ⟨24732002857253055704535881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65952007619341481878762349 24732002857253055704535881)
            ·
              refine ⟨18549002142939791778401911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24732002857253055704535881 18549002142939791778401911)
              ·
                refine ⟨27823503214409687667602867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18549002142939791778401911 27823503214409687667602867)
                ·
                  refine ⟨41735254821614531501404301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27823503214409687667602867 41735254821614531501404301)
                  ·
                    refine ⟨15650720558105449313026613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41735254821614531501404301 15650720558105449313026613)
                    ·
                      refine ⟨1467255052322385873096245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15650720558105449313026613 1467255052322385873096245)
                      ·
                        rfl

theorem cell23_2857469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 3, 5].length) (baseStart_2857469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2857469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2857469 prefixEnd_2857469 := by exact prefixLift 2857469
  have htrace : WordTrace (prefixWord ++ tailWord_2857469) baseStart_2857469 baseEnd_2857469 := by
    simpa [prefixWord, tailWord_2857469, baseEnd_2857469] using wordTrace_append hprefix tailTrace_2857469
  have hstable : (prefixWord ++ tailWord_2857469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857469).length < 2 ^ (prefixWord ++ tailWord_2857469).sum := by decide
  have hdescent : baseEnd_2857469 < baseStart_2857469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857476 : List Nat := [2, 3, 2, 3, 1, 1, 1, 2, 2, 6]
def baseStart_2857476 : Nat := 118140960795 + 2857476 * 2 ^ 59
def prefixEnd_2857476 : Nat := 4983230072969 + 3 ^ 40 * 2857476 * 2
def baseEnd_2857476 : Nat := 489086215562322448569571

theorem tailTrace_2857476 : CollatzResearch.WordTrace tailWord_2857476 prefixEnd_2857476 489086215562322448569571 := by
  unfold tailWord_2857476
  simp only [CollatzResearch.WordTrace]
  refine ⟨52110355897929972446404141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69480474530573296595205521 52110355897929972446404141)
  ·
    refine ⟨19541383461723739667401553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52110355897929972446404141 19541383461723739667401553)
    ·
      refine ⟨14656037596292804750551165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19541383461723739667401553 14656037596292804750551165)
      ·
        refine ⟨5496014098609801781456687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14656037596292804750551165 5496014098609801781456687)
        ·
          refine ⟨8244021147914702672185031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5496014098609801781456687 8244021147914702672185031)
          ·
            refine ⟨12366031721872054008277547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8244021147914702672185031 12366031721872054008277547)
            ·
              refine ⟨18549047582808081012416321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12366031721872054008277547 18549047582808081012416321)
              ·
                refine ⟨13911785687106060759312241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18549047582808081012416321 13911785687106060759312241)
                ·
                  refine ⟨10433839265329545569484181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13911785687106060759312241 10433839265329545569484181)
                  ·
                    refine ⟨489086215562322448569571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10433839265329545569484181 489086215562322448569571)
                    ·
                      rfl

theorem cell23_2857476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 2, 6].length) (baseStart_2857476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2857476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2857476 prefixEnd_2857476 := by exact prefixLift 2857476
  have htrace : WordTrace (prefixWord ++ tailWord_2857476) baseStart_2857476 baseEnd_2857476 := by
    simpa [prefixWord, tailWord_2857476, baseEnd_2857476] using wordTrace_append hprefix tailTrace_2857476
  have hstable : (prefixWord ++ tailWord_2857476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857476).length < 2 ^ (prefixWord ++ tailWord_2857476).sum := by decide
  have hdescent : baseEnd_2857476 < baseStart_2857476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857496 : List Nat := [2, 1, 2, 3, 3, 1, 2, 1, 2, 2, 4]
def baseStart_2857496 : Nat := 118140960795 + 2857496 * 2 ^ 59
def prefixEnd_2857496 : Nat := 4983230072969 + 3 ^ 40 * 2857496 * 2
def baseEnd_2857496 : Nat := 1467268916300057267458621

theorem tailTrace_2857496 : CollatzResearch.WordTrace tailWord_2857496 prefixEnd_2857496 1467268916300057267458621 := by
  unfold tailWord_2857496
  simp only [CollatzResearch.WordTrace]
  refine ⟨52110720627893744154268171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69480960837191658872357561 52110720627893744154268171)
  ·
    refine ⟨78166080941840616231402257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52110720627893744154268171 78166080941840616231402257)
    ·
      refine ⟨58624560706380462173551693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78166080941840616231402257 58624560706380462173551693)
      ·
        refine ⟨21984210264892673315081885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58624560706380462173551693 21984210264892673315081885)
        ·
          refine ⟨8244078849334752493155707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21984210264892673315081885 8244078849334752493155707)
          ·
            refine ⟨12366118274002128739733561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8244078849334752493155707 12366118274002128739733561)
            ·
              refine ⟨9274588705501596554800171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12366118274002128739733561 9274588705501596554800171)
              ·
                refine ⟨13911883058252394832200257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9274588705501596554800171 13911883058252394832200257)
                ·
                  refine ⟨10433912293689296124150193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13911883058252394832200257 10433912293689296124150193)
                  ·
                    refine ⟨7825434220266972093112645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10433912293689296124150193 7825434220266972093112645)
                    ·
                      refine ⟨1467268916300057267458621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7825434220266972093112645 1467268916300057267458621)
                      ·
                        rfl

theorem cell23_2857496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_2857496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2857496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2857496 prefixEnd_2857496 := by exact prefixLift 2857496
  have htrace : WordTrace (prefixWord ++ tailWord_2857496) baseStart_2857496 baseEnd_2857496 := by
    simpa [prefixWord, tailWord_2857496, baseEnd_2857496] using wordTrace_append hprefix tailTrace_2857496
  have hstable : (prefixWord ++ tailWord_2857496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857496).length < 2 ^ (prefixWord ++ tailWord_2857496).sum := by decide
  have hdescent : baseEnd_2857496 < baseStart_2857496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857500 : List Nat := [2, 2, 3, 1, 2, 4, 1, 1, 1, 4, 2]
def baseStart_2857500 : Nat := 118140960795 + 2857500 * 2 ^ 59
def prefixEnd_2857500 : Nat := 4983230072969 + 3 ^ 40 * 2857500 * 2
def baseEnd_2857500 : Nat := 1467270970222675251808603

theorem tailTrace_2857500 : CollatzResearch.WordTrace tailWord_2857500 prefixEnd_2857500 1467270970222675251808603 := by
  unfold tailWord_2857500
  simp only [CollatzResearch.WordTrace]
  refine ⟨52110793573886498495840977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69481058098515331327787969 52110793573886498495840977)
  ·
    refine ⟨39083095180414873871880733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52110793573886498495840977 39083095180414873871880733)
    ·
      refine ⟨14656160692655577701955275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39083095180414873871880733 14656160692655577701955275)
      ·
        refine ⟨21984241038983366552932913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14656160692655577701955275 21984241038983366552932913)
        ·
          refine ⟨16488180779237524914699685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21984241038983366552932913 16488180779237524914699685)
          ·
            refine ⟨3091533896107035921506191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16488180779237524914699685 3091533896107035921506191)
            ·
              refine ⟨4637300844160553882259287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3091533896107035921506191 4637300844160553882259287)
              ·
                refine ⟨6955951266240830823388931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4637300844160553882259287 6955951266240830823388931)
                ·
                  refine ⟨10433926899361246235083397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6955951266240830823388931 10433926899361246235083397)
                  ·
                    refine ⟨1956361293630233669078137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10433926899361246235083397 1956361293630233669078137)
                    ·
                      refine ⟨1467270970222675251808603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1956361293630233669078137 1467270970222675251808603)
                      ·
                        rfl

theorem cell23_2857500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 1, 1, 4, 2].length) (baseStart_2857500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2857500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2857500 prefixEnd_2857500 := by exact prefixLift 2857500
  have htrace : WordTrace (prefixWord ++ tailWord_2857500) baseStart_2857500 baseEnd_2857500 := by
    simpa [prefixWord, tailWord_2857500, baseEnd_2857500] using wordTrace_append hprefix tailTrace_2857500
  have hstable : (prefixWord ++ tailWord_2857500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857500).length < 2 ^ (prefixWord ++ tailWord_2857500).sum := by decide
  have hdescent : baseEnd_2857500 < baseStart_2857500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857519 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 8, 5]
def baseStart_2857519 : Nat := 118140960795 + 2857519 * 2 ^ 59
def prefixEnd_2857519 : Nat := 4983230072969 + 3 ^ 40 * 2857519 * 2
def baseEnd_2857519 : Nat := 489093575451703559157005

theorem tailTrace_2857519 : CollatzResearch.WordTrace tailWord_2857519 prefixEnd_2857519 489093575451703559157005 := by
  unfold tailWord_2857519
  simp only [CollatzResearch.WordTrace]
  refine ⟨104222280134704163236623611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69481520089802775491082407 104222280134704163236623611)
  ·
    refine ⟨156333420202056244854935417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104222280134704163236623611 156333420202056244854935417)
    ·
      refine ⟨117250065151542183641201563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156333420202056244854935417 117250065151542183641201563)
      ·
        refine ⟨175875097727313275461802345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117250065151542183641201563 175875097727313275461802345)
        ·
          refine ⟨131906323295484956596351759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175875097727313275461802345 131906323295484956596351759)
          ·
            refine ⟨197859484943227434894527639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131906323295484956596351759 197859484943227434894527639)
            ·
              refine ⟨296789227414841152341791459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197859484943227434894527639 296789227414841152341791459)
              ·
                refine ⟨445183841122261728512687189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 296789227414841152341791459 445183841122261728512687189)
                ·
                  refine ⟨5216998138151504631008053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 445183841122261728512687189 5216998138151504631008053)
                  ·
                    refine ⟨489093575451703559157005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5216998138151504631008053 489093575451703559157005)
                    ·
                      rfl

theorem cell23_2857519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 8, 5].length) (baseStart_2857519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2857519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2857519 prefixEnd_2857519 := by exact prefixLift 2857519
  have htrace : WordTrace (prefixWord ++ tailWord_2857519) baseStart_2857519 baseEnd_2857519 := by
    simpa [prefixWord, tailWord_2857519, baseEnd_2857519] using wordTrace_append hprefix tailTrace_2857519
  have hstable : (prefixWord ++ tailWord_2857519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857519).length < 2 ^ (prefixWord ++ tailWord_2857519).sum := by decide
  have hdescent : baseEnd_2857519 < baseStart_2857519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857546 : List Nat := [3, 1, 2, 1, 1, 5, 1, 1, 1, 2, 5]
def baseStart_2857546 : Nat := 118140960795 + 2857546 * 2 ^ 59
def prefixEnd_2857546 : Nat := 4983230072969 + 3 ^ 40 * 2857546 * 2
def baseEnd_2857546 : Nat := 1467294590332782071833391

theorem tailTrace_2857546 : CollatzResearch.WordTrace tailWord_2857546 prefixEnd_2857546 1467294590332782071833391 := by
  unfold tailWord_2857546
  simp only [CollatzResearch.WordTrace]
  refine ⟨26055816226401586711964123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69482176603737564565237661 26055816226401586711964123)
  ·
    refine ⟨39083724339602380067946185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26055816226401586711964123 39083724339602380067946185)
    ·
      refine ⟨29312793254701785050959639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39083724339602380067946185 29312793254701785050959639)
      ·
        refine ⟨43969189882052677576439459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29312793254701785050959639 43969189882052677576439459)
        ·
          refine ⟨65953784823079016364659189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43969189882052677576439459 65953784823079016364659189)
          ·
            refine ⟨6183167327163657784186799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65953784823079016364659189 6183167327163657784186799)
            ·
              refine ⟨9274750990745486676280199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6183167327163657784186799 9274750990745486676280199)
              ·
                refine ⟨13912126486118230014420299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9274750990745486676280199 13912126486118230014420299)
                ·
                  refine ⟨20868189729177345021630449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13912126486118230014420299 20868189729177345021630449)
                  ·
                    refine ⟨15651142296883008766222837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20868189729177345021630449 15651142296883008766222837)
                    ·
                      refine ⟨1467294590332782071833391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15651142296883008766222837 1467294590332782071833391)
                      ·
                        rfl

theorem cell23_2857546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 1, 2, 5].length) (baseStart_2857546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2857546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2857546 prefixEnd_2857546 := by exact prefixLift 2857546
  have htrace : WordTrace (prefixWord ++ tailWord_2857546) baseStart_2857546 baseEnd_2857546 := by
    simpa [prefixWord, tailWord_2857546, baseEnd_2857546] using wordTrace_append hprefix tailTrace_2857546
  have hstable : (prefixWord ++ tailWord_2857546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857546).length < 2 ^ (prefixWord ++ tailWord_2857546).sum := by decide
  have hdescent : baseEnd_2857546 < baseStart_2857546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857579 : List Nat := [1, 1, 1, 1, 2, 2, 1, 6, 8]
def baseStart_2857579 : Nat := 118140960795 + 2857579 * 2 ^ 59
def prefixEnd_2857579 : Nat := 4983230072969 + 3 ^ 40 * 2857579 * 2
def baseEnd_2857579 : Nat := 163034615021597826968971

theorem tailTrace_2857579 : CollatzResearch.WordTrace tailWord_2857579 prefixEnd_2857579 163034615021597826968971 := by
  unfold tailWord_2857579
  simp only [CollatzResearch.WordTrace]
  refine ⟨104224468514486793483807791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69482979009657862322538527 104224468514486793483807791)
  ·
    refine ⟨156336702771730190225711687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104224468514486793483807791 156336702771730190225711687)
    ·
      refine ⟨234505054157595285338567531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156336702771730190225711687 234505054157595285338567531)
      ·
        refine ⟨351757581236392928007851297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234505054157595285338567531 351757581236392928007851297)
        ·
          refine ⟨263818185927294696005888473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 351757581236392928007851297 263818185927294696005888473)
          ·
            refine ⟨197863639445471022004416355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 263818185927294696005888473 197863639445471022004416355)
            ·
              refine ⟨296795459168206533006624533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197863639445471022004416355 296795459168206533006624533)
              ·
                refine ⟨13912287148509681234685525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 296795459168206533006624533 13912287148509681234685525)
                ·
                  refine ⟨163034615021597826968971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13912287148509681234685525 163034615021597826968971)
                  ·
                    rfl

theorem cell23_2857579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 8].length) (baseStart_2857579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2857579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2857579 prefixEnd_2857579 := by exact prefixLift 2857579
  have htrace : WordTrace (prefixWord ++ tailWord_2857579) baseStart_2857579 baseEnd_2857579 := by
    simpa [prefixWord, tailWord_2857579, baseEnd_2857579] using wordTrace_append hprefix tailTrace_2857579
  have hstable : (prefixWord ++ tailWord_2857579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857579).length < 2 ^ (prefixWord ++ tailWord_2857579).sum := by decide
  have hdescent : baseEnd_2857579 < baseStart_2857579 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857593 : List Nat := [1, 2, 1, 3, 3, 2, 2, 2, 2, 2, 3]
def baseStart_2857593 : Nat := 118140960795 + 2857593 * 2 ^ 59
def prefixEnd_2857593 : Nat := 4983230072969 + 3 ^ 40 * 2857593 * 2
def baseEnd_2857593 : Nat := 1467318723923543387945675

theorem tailTrace_2857593 : CollatzResearch.WordTrace tailWord_2857593 prefixEnd_2857593 1467318723923543387945675 := by
  unfold tailWord_2857593
  simp only [CollatzResearch.WordTrace]
  refine ⟨104224979136436073874817433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69483319424290715916544955 104224979136436073874817433)
  ·
    refine ⟨78168734352327055406113075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104224979136436073874817433 78168734352327055406113075)
    ·
      refine ⟨117253101528490583109169613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78168734352327055406113075 117253101528490583109169613)
      ·
        refine ⟨43969913073183968665938605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117253101528490583109169613 43969913073183968665938605)
        ·
          refine ⟨16488717402443988249726977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43969913073183968665938605 16488717402443988249726977)
          ·
            refine ⟨12366538051832991187295233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16488717402443988249726977 12366538051832991187295233)
            ·
              refine ⟨9274903538874743390471425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12366538051832991187295233 9274903538874743390471425)
              ·
                refine ⟨6956177654156057542853569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9274903538874743390471425 6956177654156057542853569)
                ·
                  refine ⟨5217133240617043157140177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6956177654156057542853569 5217133240617043157140177)
                  ·
                    refine ⟨3912849930462782367855133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5217133240617043157140177 3912849930462782367855133)
                    ·
                      refine ⟨1467318723923543387945675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3912849930462782367855133 1467318723923543387945675)
                      ·
                        rfl

theorem cell23_2857593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 2, 2, 2, 3].length) (baseStart_2857593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2857593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2857593 prefixEnd_2857593 := by exact prefixLift 2857593
  have htrace : WordTrace (prefixWord ++ tailWord_2857593) baseStart_2857593 baseEnd_2857593 := by
    simpa [prefixWord, tailWord_2857593, baseEnd_2857593] using wordTrace_append hprefix tailTrace_2857593
  have hstable : (prefixWord ++ tailWord_2857593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857593).length < 2 ^ (prefixWord ++ tailWord_2857593).sum := by decide
  have hdescent : baseEnd_2857593 < baseStart_2857593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857596 : List Nat := [2, 2, 2, 1, 1, 2, 3, 4, 6]
def baseStart_2857596 : Nat := 118140960795 + 2857596 * 2 ^ 59
def prefixEnd_2857596 : Nat := 4983230072969 + 3 ^ 40 * 2857596 * 2
def baseEnd_2857596 : Nat := 163035584929500764023129

theorem tailTrace_2857596 : CollatzResearch.WordTrace tailWord_2857596 prefixEnd_2857596 163035584929500764023129 := by
  unfold tailWord_2857596
  simp only [CollatzResearch.WordTrace]
  refine ⟨52112544277712602693588321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69483392370283470258117761 52112544277712602693588321)
  ·
    refine ⟨39084408208284452020191241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52112544277712602693588321 39084408208284452020191241)
    ·
      refine ⟨29313306156213339015143431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39084408208284452020191241 29313306156213339015143431)
      ·
        refine ⟨43969959234320008522715147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29313306156213339015143431 43969959234320008522715147)
        ·
          refine ⟨65954938851480012784072721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43969959234320008522715147 65954938851480012784072721)
          ·
            refine ⟨49466204138610009588054541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65954938851480012784072721 49466204138610009588054541)
            ·
              refine ⟨18549826551978753595520453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49466204138610009588054541 18549826551978753595520453)
              ·
                refine ⟨3478092478496016299160085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18549826551978753595520453 3478092478496016299160085)
                ·
                  refine ⟨163035584929500764023129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3478092478496016299160085 163035584929500764023129)
                  ·
                    rfl

theorem cell23_2857596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 4, 6].length) (baseStart_2857596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2857596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2857596 prefixEnd_2857596 := by exact prefixLift 2857596
  have htrace : WordTrace (prefixWord ++ tailWord_2857596) baseStart_2857596 baseEnd_2857596 := by
    simpa [prefixWord, tailWord_2857596, baseEnd_2857596] using wordTrace_append hprefix tailTrace_2857596
  have hstable : (prefixWord ++ tailWord_2857596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857596).length < 2 ^ (prefixWord ++ tailWord_2857596).sum := by decide
  have hdescent : baseEnd_2857596 < baseStart_2857596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857600 : List Nat := [2, 1, 1, 2, 1, 6, 1, 4, 1, 4]
def baseStart_2857600 : Nat := 118140960795 + 2857600 * 2 ^ 59
def prefixEnd_2857600 : Nat := 4983230072969 + 3 ^ 40 * 2857600 * 2
def baseEnd_2857600 : Nat := 489107439429374953519381

theorem tailTrace_2857600 : CollatzResearch.WordTrace tailWord_2857600 prefixEnd_2857600 489107439429374953519381 := by
  unfold tailWord_2857600
  simp only [CollatzResearch.WordTrace]
  refine ⟨52112617223705357035161127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69483489631607142713548169 52112617223705357035161127)
  ·
    refine ⟨78168925835558035552741691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52112617223705357035161127 78168925835558035552741691)
    ·
      refine ⟨117253388753337053329112537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78168925835558035552741691 117253388753337053329112537)
      ·
        refine ⟨87940041565002789996834403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117253388753337053329112537 87940041565002789996834403)
        ·
          refine ⟨131910062347504184995251605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87940041565002789996834403 131910062347504184995251605)
          ·
            refine ⟨6183284172539258671652419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 131910062347504184995251605 6183284172539258671652419)
            ·
              refine ⟨9274926258808888007478629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6183284172539258671652419 9274926258808888007478629)
              ·
                refine ⟨1739048673526666501402243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9274926258808888007478629 1739048673526666501402243)
                ·
                  refine ⟨2608573010289999752103365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1739048673526666501402243 2608573010289999752103365)
                  ·
                    refine ⟨489107439429374953519381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2608573010289999752103365 489107439429374953519381)
                    ·
                      rfl

theorem cell23_2857600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 4, 1, 4].length) (baseStart_2857600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2857600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2857600 prefixEnd_2857600 := by exact prefixLift 2857600
  have htrace : WordTrace (prefixWord ++ tailWord_2857600) baseStart_2857600 baseEnd_2857600 := by
    simpa [prefixWord, tailWord_2857600, baseEnd_2857600] using wordTrace_append hprefix tailTrace_2857600
  have hstable : (prefixWord ++ tailWord_2857600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857600).length < 2 ^ (prefixWord ++ tailWord_2857600).sum := by decide
  have hdescent : baseEnd_2857600 < baseStart_2857600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857700 : List Nat := [2, 3, 1, 1, 1, 4, 2, 3, 1, 2, 3]
def baseStart_2857700 : Nat := 118140960795 + 2857700 * 2 ^ 59
def prefixEnd_2857700 : Nat := 4983230072969 + 3 ^ 40 * 2857700 * 2
def baseEnd_2857700 : Nat := 1467373666353574469307683

theorem tailTrace_2857700 : CollatzResearch.WordTrace tailWord_2857700 prefixEnd_2857700 1467373666353574469307683 := by
  unfold tailWord_2857700
  simp only [CollatzResearch.WordTrace]
  refine ⟨52114440873524215574481277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69485921164698954099308369 52114440873524215574481277)
  ·
    refine ⟨19542915327571580840430479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52114440873524215574481277 19542915327571580840430479)
    ·
      refine ⟨29314372991357371260645719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19542915327571580840430479 29314372991357371260645719)
      ·
        refine ⟨43971559487036056890968579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29314372991357371260645719 43971559487036056890968579)
        ·
          refine ⟨65957339230554085336452869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43971559487036056890968579 65957339230554085336452869)
          ·
            refine ⟨12367001105728891000584913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65957339230554085336452869 12367001105728891000584913)
            ·
              refine ⟨9275250829296668250438685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12367001105728891000584913 9275250829296668250438685)
              ·
                refine ⟨3478219060986250593914507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9275250829296668250438685 3478219060986250593914507)
                ·
                  refine ⟨5217328591479375890871761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3478219060986250593914507 5217328591479375890871761)
                  ·
                    refine ⟨3912996443609531918153821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5217328591479375890871761 3912996443609531918153821)
                    ·
                      refine ⟨1467373666353574469307683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3912996443609531918153821 1467373666353574469307683)
                      ·
                        rfl

theorem cell23_2857700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 3, 1, 2, 3].length) (baseStart_2857700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2857700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2857700 prefixEnd_2857700 := by exact prefixLift 2857700
  have htrace : WordTrace (prefixWord ++ tailWord_2857700) baseStart_2857700 baseEnd_2857700 := by
    simpa [prefixWord, tailWord_2857700, baseEnd_2857700] using wordTrace_append hprefix tailTrace_2857700
  have hstable : (prefixWord ++ tailWord_2857700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857700).length < 2 ^ (prefixWord ++ tailWord_2857700).sum := by decide
  have hdescent : baseEnd_2857700 < baseStart_2857700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857714 : List Nat := [3, 2, 1, 3, 1, 4, 1, 1, 3, 2, 2]
def baseStart_2857714 : Nat := 118140960795 + 2857714 * 2 ^ 59
def prefixEnd_2857714 : Nat := 4983230072969 + 3 ^ 40 * 2857714 * 2
def baseEnd_2857714 : Nat := 1467380855082737414532619

theorem tailTrace_2857714 : CollatzResearch.WordTrace tailWord_2857714 prefixEnd_2857714 1467380855082737414532619 := by
  unfold tailWord_2857714
  simp only [CollatzResearch.WordTrace]
  refine ⟨26057348092249427884993049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69486261579331807693314797 26057348092249427884993049)
  ·
    refine ⟨19543011069187070913744787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26057348092249427884993049 19543011069187070913744787)
    ·
      refine ⟨29314516603780606370617181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19543011069187070913744787 29314516603780606370617181)
      ·
        refine ⟨10992943726417727388981443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29314516603780606370617181 10992943726417727388981443)
        ·
          refine ⟨16489415589626591083472165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10992943726417727388981443 16489415589626591083472165)
          ·
            refine ⟨3091765423054985828151031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16489415589626591083472165 3091765423054985828151031)
            ·
              refine ⟨4637648134582478742226547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3091765423054985828151031 4637648134582478742226547)
              ·
                refine ⟨6956472201873718113339821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4637648134582478742226547 6956472201873718113339821)
                ·
                  refine ⟨2608677075702644292502433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6956472201873718113339821 2608677075702644292502433)
                  ·
                    refine ⟨1956507806776983219376825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2608677075702644292502433 1956507806776983219376825)
                    ·
                      refine ⟨1467380855082737414532619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1956507806776983219376825 1467380855082737414532619)
                      ·
                        rfl

theorem cell23_2857714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 1, 3, 2, 2].length) (baseStart_2857714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2857714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2857714 prefixEnd_2857714 := by exact prefixLift 2857714
  have htrace : WordTrace (prefixWord ++ tailWord_2857714) baseStart_2857714 baseEnd_2857714 := by
    simpa [prefixWord, tailWord_2857714, baseEnd_2857714] using wordTrace_append hprefix tailTrace_2857714
  have hstable : (prefixWord ++ tailWord_2857714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857714).length < 2 ^ (prefixWord ++ tailWord_2857714).sum := by decide
  have hdescent : baseEnd_2857714 < baseStart_2857714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857764 : List Nat := [2, 3, 1, 3, 3, 1, 2, 2, 2, 1, 3]
def baseStart_2857764 : Nat := 118140960795 + 2857764 * 2 ^ 59
def prefixEnd_2857764 : Nat := 4983230072969 + 3 ^ 40 * 2857764 * 2
def baseEnd_2857764 : Nat := 1467406529115462218907389

theorem tailTrace_2857764 : CollatzResearch.WordTrace tailWord_2857764 prefixEnd_2857764 1467406529115462218907389 := by
  unfold tailWord_2857764
  simp only [CollatzResearch.WordTrace]
  refine ⟨52115608009408285039646173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69487477345877713386194897 52115608009408285039646173)
  ·
    refine ⟨19543353003528106889867315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52115608009408285039646173 19543353003528106889867315)
    ·
      refine ⟨29315029505292160334800973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19543353003528106889867315 29315029505292160334800973)
      ·
        refine ⟨10993136064484560125550365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29315029505292160334800973 10993136064484560125550365)
        ·
          refine ⟨4122426024181710047081387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10993136064484560125550365 4122426024181710047081387)
          ·
            refine ⟨6183639036272565070622081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4122426024181710047081387 6183639036272565070622081)
            ·
              refine ⟨4637729277204423802966561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6183639036272565070622081 4637729277204423802966561)
              ·
                refine ⟨3478296957903317852224921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4637729277204423802966561 3478296957903317852224921)
                ·
                  refine ⟨2608722718427488389168691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3478296957903317852224921 2608722718427488389168691)
                  ·
                    refine ⟨3913084077641232583753037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2608722718427488389168691 3913084077641232583753037)
                    ·
                      refine ⟨1467406529115462218907389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3913084077641232583753037 1467406529115462218907389)
                      ·
                        rfl

theorem cell23_2857764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_2857764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2857764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2857764 prefixEnd_2857764 := by exact prefixLift 2857764
  have htrace : WordTrace (prefixWord ++ tailWord_2857764) baseStart_2857764 baseEnd_2857764 := by
    simpa [prefixWord, tailWord_2857764, baseEnd_2857764] using wordTrace_append hprefix tailTrace_2857764
  have hstable : (prefixWord ++ tailWord_2857764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857764).length < 2 ^ (prefixWord ++ tailWord_2857764).sum := by decide
  have hdescent : baseEnd_2857764 < baseStart_2857764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857776 : List Nat := [2, 1, 1, 1, 2, 2, 1, 2, 11]
def baseStart_2857776 : Nat := 118140960795 + 2857776 * 2 ^ 59
def prefixEnd_2857776 : Nat := 4983230072969 + 3 ^ 40 * 2857776 * 2
def baseEnd_2857776 : Nat := 163045854542590685773037

theorem tailTrace_2857776 : CollatzResearch.WordTrace tailWord_2857776 prefixEnd_2857776 163045854542590685773037 := by
  unfold tailWord_2857776
  simp only [CollatzResearch.WordTrace]
  refine ⟨52115826847386548064364591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69487769129848730752486121 52115826847386548064364591)
  ·
    refine ⟨78173740271079822096546887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52115826847386548064364591 78173740271079822096546887)
    ·
      refine ⟨117260610406619733144820331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78173740271079822096546887 117260610406619733144820331)
      ·
        refine ⟨175890915609929599717230497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117260610406619733144820331 175890915609929599717230497)
        ·
          refine ⟨131918186707447199787922873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175890915609929599717230497 131918186707447199787922873)
          ·
            refine ⟨98938640030585399840942155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131918186707447199787922873 98938640030585399840942155)
            ·
              refine ⟨148407960045878099761413233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98938640030585399840942155 148407960045878099761413233)
              ·
                refine ⟨111305970034408574821059925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148407960045878099761413233 111305970034408574821059925)
                ·
                  refine ⟨163045854542590685773037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 111305970034408574821059925 163045854542590685773037)
                  ·
                    rfl

theorem cell23_2857776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 11].length) (baseStart_2857776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2857776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2857776 prefixEnd_2857776 := by exact prefixLift 2857776
  have htrace : WordTrace (prefixWord ++ tailWord_2857776) baseStart_2857776 baseEnd_2857776 := by
    simpa [prefixWord, tailWord_2857776, baseEnd_2857776] using wordTrace_append hprefix tailTrace_2857776
  have hstable : (prefixWord ++ tailWord_2857776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857776).length < 2 ^ (prefixWord ++ tailWord_2857776).sum := by decide
  have hdescent : baseEnd_2857776 < baseStart_2857776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857783 : List Nat := [1, 1, 3, 1, 2, 1, 5, 1, 2, 2, 4]
def baseStart_2857783 : Nat := 118140960795 + 2857783 * 2 ^ 59
def prefixEnd_2857783 : Nat := 4983230072969 + 3 ^ 40 * 2857783 * 2
def baseEnd_2857783 : Nat := 1467416285247897644569801

theorem tailTrace_2857783 : CollatzResearch.WordTrace tailWord_2857783 prefixEnd_2857783 1467416285247897644569801 := by
  unfold tailWord_2857783
  simp only [CollatzResearch.WordTrace]
  refine ⟨104231909005747736324234003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69487939337165157549489335 104231909005747736324234003)
  ·
    refine ⟨156347863508621604486351005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104231909005747736324234003 156347863508621604486351005)
    ·
      refine ⟨58630448815733101682381627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156347863508621604486351005 58630448815733101682381627)
      ·
        refine ⟨87945673223599652523572441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58630448815733101682381627 87945673223599652523572441)
        ·
          refine ⟨65959254917699739392679331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87945673223599652523572441 65959254917699739392679331)
          ·
            refine ⟨98938882376549609089018997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65959254917699739392679331 98938882376549609089018997)
            ·
              refine ⟨9275520222801525852095531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 98938882376549609089018997 9275520222801525852095531)
              ·
                refine ⟨13913280334202288778143297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9275520222801525852095531 13913280334202288778143297)
                ·
                  refine ⟨10434960250651716583607473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13913280334202288778143297 10434960250651716583607473)
                  ·
                    refine ⟨7826220187988787437705605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10434960250651716583607473 7826220187988787437705605)
                    ·
                      refine ⟨1467416285247897644569801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7826220187988787437705605 1467416285247897644569801)
                      ·
                        rfl

theorem cell23_2857783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 2, 2, 4].length) (baseStart_2857783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2857783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2857783 prefixEnd_2857783 := by exact prefixLift 2857783
  have htrace : WordTrace (prefixWord ++ tailWord_2857783) baseStart_2857783 baseEnd_2857783 := by
    simpa [prefixWord, tailWord_2857783, baseEnd_2857783] using wordTrace_append hprefix tailTrace_2857783
  have hstable : (prefixWord ++ tailWord_2857783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857783).length < 2 ^ (prefixWord ++ tailWord_2857783).sum := by decide
  have hdescent : baseEnd_2857783 < baseStart_2857783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857823 : List Nat := [1, 1, 2, 3, 1, 3, 2, 1, 4, 5]
def baseStart_2857823 : Nat := 118140960795 + 2857823 * 2 ^ 59
def prefixEnd_2857823 : Nat := 4983230072969 + 3 ^ 40 * 2857823 * 2
def baseEnd_2857823 : Nat := 489145608158025829356539

theorem tailTrace_2857823 : CollatzResearch.WordTrace tailWord_2857823 prefixEnd_2857823 489145608158025829356539 := by
  unfold tailWord_2857823
  simp only [CollatzResearch.WordTrace]
  refine ⟨104233367925602823155690123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69488911950401882103793415 104233367925602823155690123)
  ·
    refine ⟨156350051888404234733535185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104233367925602823155690123 156350051888404234733535185)
    ·
      refine ⟨117262538916303176050151389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156350051888404234733535185 117262538916303176050151389)
      ·
        refine ⟨43973452093613691018806771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117262538916303176050151389 43973452093613691018806771)
        ·
          refine ⟨65960178140420536528210157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43973452093613691018806771 65960178140420536528210157)
          ·
            refine ⟨24735066802657701198078809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65960178140420536528210157 24735066802657701198078809)
            ·
              refine ⟨18551300101993275898559107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24735066802657701198078809 18551300101993275898559107)
              ·
                refine ⟨27826950152989913847838661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18551300101993275898559107 27826950152989913847838661)
                ·
                  refine ⟨5217553153685608846469749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27826950152989913847838661 5217553153685608846469749)
                  ·
                    refine ⟨489145608158025829356539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5217553153685608846469749 489145608158025829356539)
                    ·
                      rfl

theorem cell23_2857823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 4, 5].length) (baseStart_2857823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2857823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2857823 prefixEnd_2857823 := by exact prefixLift 2857823
  have htrace : WordTrace (prefixWord ++ tailWord_2857823) baseStart_2857823 baseEnd_2857823 := by
    simpa [prefixWord, tailWord_2857823, baseEnd_2857823] using wordTrace_append hprefix tailTrace_2857823
  have hstable : (prefixWord ++ tailWord_2857823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857823).length < 2 ^ (prefixWord ++ tailWord_2857823).sum := by decide
  have hdescent : baseEnd_2857823 < baseStart_2857823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857838 : List Nat := [4, 1, 2, 3, 2, 1, 3, 1, 2, 2, 2]
def baseStart_2857838 : Nat := 118140960795 + 2857838 * 2 ^ 59
def prefixEnd_2857838 : Nat := 4983230072969 + 3 ^ 40 * 2857838 * 2
def baseEnd_2857838 : Nat := 1467444526683894929382049

theorem tailTrace_2857838 : CollatzResearch.WordTrace tailWord_2857838 prefixEnd_2857838 1467444526683894929382049 := by
  unfold tailWord_2857838
  simp only [CollatzResearch.WordTrace]
  refine ⟨13029239377568560089685771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69489276680365653811657445 13029239377568560089685771)
  ·
    refine ⟨19543859066352840134528657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13029239377568560089685771 19543859066352840134528657)
    ·
      refine ⟨14657894299764630100896493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19543859066352840134528657 14657894299764630100896493)
      ·
        refine ⟨5496710362411736287836185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14657894299764630100896493 5496710362411736287836185)
        ·
          refine ⟨4122532771808802215877139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5496710362411736287836185 4122532771808802215877139)
          ·
            refine ⟨6183799157713203323815709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4122532771808802215877139 6183799157713203323815709)
            ·
              refine ⟨2318924684142451246430891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6183799157713203323815709 2318924684142451246430891)
              ·
                refine ⟨3478387026213676869646337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2318924684142451246430891 3478387026213676869646337)
                ·
                  refine ⟨2608790269660257652234753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3478387026213676869646337 2608790269660257652234753)
                  ·
                    refine ⟨1956592702245193239176065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2608790269660257652234753 1956592702245193239176065)
                    ·
                      refine ⟨1467444526683894929382049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1956592702245193239176065 1467444526683894929382049)
                      ·
                        rfl

theorem cell23_2857838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_2857838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2857838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2857838 prefixEnd_2857838 := by exact prefixLift 2857838
  have htrace : WordTrace (prefixWord ++ tailWord_2857838) baseStart_2857838 baseEnd_2857838 := by
    simpa [prefixWord, tailWord_2857838, baseEnd_2857838] using wordTrace_append hprefix tailTrace_2857838
  have hstable : (prefixWord ++ tailWord_2857838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857838).length < 2 ^ (prefixWord ++ tailWord_2857838).sum := by decide
  have hdescent : baseEnd_2857838 < baseStart_2857838 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857843 : List Nat := [1, 1, 1, 2, 2, 1, 5, 2, 1, 3, 4]
def baseStart_2857843 : Nat := 118140960795 + 2857843 * 2 ^ 59
def prefixEnd_2857843 : Nat := 4983230072969 + 3 ^ 40 * 2857843 * 2
def baseEnd_2857843 : Nat := 1467447094087167409819525

theorem tailTrace_2857843 : CollatzResearch.WordTrace tailWord_2857843 prefixEnd_2857843 1467447094087167409819525 := by
  unfold tailWord_2857843
  simp only [CollatzResearch.WordTrace]
  refine ⟨104234097385530366571418183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69489398257020244380945455 104234097385530366571418183)
  ·
    refine ⟨156351146078295549857127275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104234097385530366571418183 156351146078295549857127275)
    ·
      refine ⟨234526719117443324785690913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156351146078295549857127275 234526719117443324785690913)
      ·
        refine ⟨175895039338082493589268185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234526719117443324785690913 175895039338082493589268185)
        ·
          refine ⟨131921279503561870191951139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175895039338082493589268185 131921279503561870191951139)
          ·
            refine ⟨197881919255342805287926709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131921279503561870191951139 197881919255342805287926709)
            ·
              refine ⟨18551429930188387995743129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 197881919255342805287926709 18551429930188387995743129)
              ·
                refine ⟨13913572447641290996807347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18551429930188387995743129 13913572447641290996807347)
                ·
                  refine ⟨20870358671461936495211021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13913572447641290996807347 20870358671461936495211021)
                  ·
                    refine ⟨7826384501798226185704133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20870358671461936495211021 7826384501798226185704133)
                    ·
                      refine ⟨1467447094087167409819525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7826384501798226185704133 1467447094087167409819525)
                      ·
                        rfl

theorem cell23_2857843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 3, 4].length) (baseStart_2857843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2857843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2857843 prefixEnd_2857843 := by exact prefixLift 2857843
  have htrace : WordTrace (prefixWord ++ tailWord_2857843) baseStart_2857843 baseEnd_2857843 := by
    simpa [prefixWord, tailWord_2857843, baseEnd_2857843] using wordTrace_append hprefix tailTrace_2857843
  have hstable : (prefixWord ++ tailWord_2857843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857843).length < 2 ^ (prefixWord ++ tailWord_2857843).sum := by decide
  have hdescent : baseEnd_2857843 < baseStart_2857843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857860 : List Nat := [2, 3, 2, 1, 1, 1, 1, 5, 2, 1, 4]
def baseStart_2857860 : Nat := 118140960795 + 2857860 * 2 ^ 59
def prefixEnd_2857860 : Nat := 4983230072969 + 3 ^ 40 * 2857860 * 2
def baseEnd_2857860 : Nat := 1467455823258293843306947

theorem tailTrace_2857860 : CollatzResearch.WordTrace tailWord_2857860 prefixEnd_2857860 1467455823258293843306947 := by
  unfold tailWord_2857860
  simp only [CollatzResearch.WordTrace]
  refine ⟨52117358713234389237393517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69489811617645852316524689 52117358713234389237393517)
  ·
    refine ⟨19544009517462895964022569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52117358713234389237393517 19544009517462895964022569)
    ·
      refine ⟨14658007138097171973016927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19544009517462895964022569 14658007138097171973016927)
      ·
        refine ⟨21987010707145757959525391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14658007138097171973016927 21987010707145757959525391)
        ·
          refine ⟨32980516060718636939288087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21987010707145757959525391 32980516060718636939288087)
          ·
            refine ⟨49470774091077955408932131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32980516060718636939288087 49470774091077955408932131)
            ·
              refine ⟨74206161136616933113398197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49470774091077955408932131 74206161136616933113398197)
              ·
                refine ⟨6956827606557837479381081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74206161136616933113398197 6956827606557837479381081)
                ·
                  refine ⟨5217620704918378109535811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6956827606557837479381081 5217620704918378109535811)
                  ·
                    refine ⟨7826431057377567164303717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5217620704918378109535811 7826431057377567164303717)
                    ·
                      refine ⟨1467455823258293843306947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7826431057377567164303717 1467455823258293843306947)
                      ·
                        rfl

theorem cell23_2857860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_2857860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2857860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2857860 prefixEnd_2857860 := by exact prefixLift 2857860
  have htrace : WordTrace (prefixWord ++ tailWord_2857860) baseStart_2857860 baseEnd_2857860 := by
    simpa [prefixWord, tailWord_2857860, baseEnd_2857860] using wordTrace_append hprefix tailTrace_2857860
  have hstable : (prefixWord ++ tailWord_2857860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857860).length < 2 ^ (prefixWord ++ tailWord_2857860).sum := by decide
  have hdescent : baseEnd_2857860 < baseStart_2857860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857878 : List Nat := [5, 3, 1, 1, 1, 2, 3, 2, 5]
def baseStart_2857878 : Nat := 118140960795 + 2857878 * 2 ^ 59
def prefixEnd_2857878 : Nat := 4983230072969 + 3 ^ 40 * 2857878 * 2
def baseEnd_2857878 : Nat := 163051673990008308097985

theorem tailTrace_2857878 : CollatzResearch.WordTrace tailWord_2857878 prefixEnd_2857878 163051673990008308097985 := by
  unfold tailWord_2857878
  simp only [CollatzResearch.WordTrace]
  refine ⟨6514710871275222971808893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69490249293602378365961525 6514710871275222971808893)
  ·
    refine ⟨2443016576728208614428335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6514710871275222971808893 2443016576728208614428335)
    ·
      refine ⟨3664524865092312921642503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2443016576728208614428335 3664524865092312921642503)
      ·
        refine ⟨5496787297638469382463755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3664524865092312921642503 5496787297638469382463755)
        ·
          refine ⟨8245180946457704073695633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5496787297638469382463755 8245180946457704073695633)
          ·
            refine ⟨6183885709843278055271725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8245180946457704073695633 6183885709843278055271725)
            ·
              refine ⟨2318957141191229270726897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6183885709843278055271725 2318957141191229270726897)
              ·
                refine ⟨1739217855893421953045173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2318957141191229270726897 1739217855893421953045173)
                ·
                  refine ⟨163051673990008308097985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1739217855893421953045173 163051673990008308097985)
                  ·
                    rfl

theorem cell23_2857878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_2857878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2857878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2857878 prefixEnd_2857878 := by exact prefixLift 2857878
  have htrace : WordTrace (prefixWord ++ tailWord_2857878) baseStart_2857878 baseEnd_2857878 := by
    simpa [prefixWord, tailWord_2857878, baseEnd_2857878] using wordTrace_append hprefix tailTrace_2857878
  have hstable : (prefixWord ++ tailWord_2857878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857878).length < 2 ^ (prefixWord ++ tailWord_2857878).sum := by decide
  have hdescent : baseEnd_2857878 < baseStart_2857878 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857887 : List Nat := [1, 1, 2, 5, 2, 1, 3, 1, 3, 4]
def baseStart_2857887 : Nat := 118140960795 + 2857887 * 2 ^ 59
def prefixEnd_2857887 : Nat := 4983230072969 + 3 ^ 40 * 2857887 * 2
def baseEnd_2857887 : Nat := 489156562411988412556441

theorem tailTrace_2857887 : CollatzResearch.WordTrace tailWord_2857887 prefixEnd_2857887 489156562411988412556441 := by
  unfold tailWord_2857887
  simp only [CollatzResearch.WordTrace]
  refine ⟨104235702197370962086019915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69490468131580641390679943 104235702197370962086019915)
  ·
    refine ⟨156353553296056443129029873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104235702197370962086019915 156353553296056443129029873)
    ·
      refine ⟨117265164972042332346772405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156353553296056443129029873 117265164972042332346772405)
      ·
        refine ⟨10993609216128968657509913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 117265164972042332346772405 10993609216128968657509913)
        ·
          refine ⟨8245206912096726493132435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10993609216128968657509913 8245206912096726493132435)
          ·
            refine ⟨12367810368145089739698653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8245206912096726493132435 12367810368145089739698653)
            ·
              refine ⟨4637928888054408652386995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12367810368145089739698653 4637928888054408652386995)
              ·
                refine ⟨6956893332081612978580493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4637928888054408652386995 6956893332081612978580493)
                ·
                  refine ⟨2608834999530604866967685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6956893332081612978580493 2608834999530604866967685)
                  ·
                    refine ⟨489156562411988412556441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2608834999530604866967685 489156562411988412556441)
                    ·
                      rfl

theorem cell23_2857887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 1, 3, 4].length) (baseStart_2857887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2857887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2857887 prefixEnd_2857887 := by exact prefixLift 2857887
  have htrace : WordTrace (prefixWord ++ tailWord_2857887) baseStart_2857887 baseEnd_2857887 := by
    simpa [prefixWord, tailWord_2857887, baseEnd_2857887] using wordTrace_append hprefix tailTrace_2857887
  have hstable : (prefixWord ++ tailWord_2857887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857887).length < 2 ^ (prefixWord ++ tailWord_2857887).sum := by decide
  have hdescent : baseEnd_2857887 < baseStart_2857887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857937 : List Nat := [1, 2, 2, 1, 2, 1, 3, 4, 2, 3, 2]
def baseStart_2857937 : Nat := 118140960795 + 2857937 * 2 ^ 59
def prefixEnd_2857937 : Nat := 4983230072969 + 3 ^ 40 * 2857937 * 2
def baseEnd_2857937 : Nat := 1467495361268690042044093

theorem tailTrace_2857937 : CollatzResearch.WordTrace tailWord_2857937 prefixEnd_2857937 1467495361268690042044093 := by
  unfold tailWord_2857937
  simp only [CollatzResearch.WordTrace]
  refine ⟨104237525847189820625340065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69491683898126547083560043 104237525847189820625340065)
  ·
    refine ⟨78178144385392365469005049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104237525847189820625340065 78178144385392365469005049)
    ·
      refine ⟨58633608289044274101753787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78178144385392365469005049 58633608289044274101753787)
      ·
        refine ⟨87950412433566411152630681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58633608289044274101753787 87950412433566411152630681)
        ·
          refine ⟨65962809325174808364473011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87950412433566411152630681 65962809325174808364473011)
          ·
            refine ⟨98944213987762212546709517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65962809325174808364473011 98944213987762212546709517)
            ·
              refine ⟨37104080245410829705016069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98944213987762212546709517 37104080245410829705016069)
              ·
                refine ⟨6957015046014530569690513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37104080245410829705016069 6957015046014530569690513)
                ·
                  refine ⟨5217761284510897927267885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6957015046014530569690513 5217761284510897927267885)
                  ·
                    refine ⟨1956660481691586722725457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5217761284510897927267885 1956660481691586722725457)
                    ·
                      refine ⟨1467495361268690042044093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1956660481691586722725457 1467495361268690042044093)
                      ·
                        rfl

theorem cell23_2857937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 4, 2, 3, 2].length) (baseStart_2857937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2857937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2857937 prefixEnd_2857937 := by exact prefixLift 2857937
  have htrace : WordTrace (prefixWord ++ tailWord_2857937) baseStart_2857937 baseEnd_2857937 := by
    simpa [prefixWord, tailWord_2857937, baseEnd_2857937] using wordTrace_append hprefix tailTrace_2857937
  have hstable : (prefixWord ++ tailWord_2857937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857937).length < 2 ^ (prefixWord ++ tailWord_2857937).sum := by decide
  have hdescent : baseEnd_2857937 < baseStart_2857937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857938 : List Nat := [3, 2, 2, 3, 1, 3, 2, 2, 1, 4]
def baseStart_2857938 : Nat := 118140960795 + 2857938 * 2 ^ 59
def prefixEnd_2857938 : Nat := 4983230072969 + 3 ^ 40 * 2857938 * 2
def baseEnd_2857938 : Nat := 489165291583114846043863

theorem tailTrace_2857938 : CollatzResearch.WordTrace tailWord_2857938 prefixEnd_2857938 489165291583114846043863 := by
  unfold tailWord_2857938
  simp only [CollatzResearch.WordTrace]
  refine ⟨26059390580046549449031617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69491708213457465197417645 26059390580046549449031617)
  ·
    refine ⟨19544542935034912086773713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26059390580046549449031617 19544542935034912086773713)
    ·
      refine ⟨14658407201276184065080285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19544542935034912086773713 14658407201276184065080285)
      ·
        refine ⟨5496902700478569024405107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14658407201276184065080285 5496902700478569024405107)
        ·
          refine ⟨8245354050717853536607661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5496902700478569024405107 8245354050717853536607661)
          ·
            refine ⟨3092007769019195076227873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8245354050717853536607661 3092007769019195076227873)
            ·
              refine ⟨2319005826764396307170905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3092007769019195076227873 2319005826764396307170905)
              ·
                refine ⟨1739254370073297230378179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2319005826764396307170905 1739254370073297230378179)
                ·
                  refine ⟨2608881555109945845567269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1739254370073297230378179 2608881555109945845567269)
                  ·
                    refine ⟨489165291583114846043863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2608881555109945845567269 489165291583114846043863)
                    ·
                      rfl

theorem cell23_2857938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 2, 2, 1, 4].length) (baseStart_2857938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2857938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2857938 prefixEnd_2857938 := by exact prefixLift 2857938
  have htrace : WordTrace (prefixWord ++ tailWord_2857938) baseStart_2857938 baseEnd_2857938 := by
    simpa [prefixWord, tailWord_2857938, baseEnd_2857938] using wordTrace_append hprefix tailTrace_2857938
  have hstable : (prefixWord ++ tailWord_2857938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857938).length < 2 ^ (prefixWord ++ tailWord_2857938).sum := by decide
  have hdescent : baseEnd_2857938 < baseStart_2857938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857960 : List Nat := [2, 1, 4, 1, 1, 1, 3, 3, 1, 6]
def baseStart_2857960 : Nat := 118140960795 + 2857960 * 2 ^ 59
def prefixEnd_2857960 : Nat := 4983230072969 + 3 ^ 40 * 2857960 * 2
def baseEnd_2857960 : Nat := 489169057107914484018829

theorem tailTrace_2857960 : CollatzResearch.WordTrace tailWord_2857960 prefixEnd_2857960 489169057107914484018829 := by
  unfold tailWord_2857960
  simp only [CollatzResearch.WordTrace]
  refine ⟨52119182363053247776713667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69492243150737663702284889 52119182363053247776713667)
  ·
    refine ⟨78178773544579871665070501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52119182363053247776713667 78178773544579871665070501)
    ·
      refine ⟨14658520039608725937200719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78178773544579871665070501 14658520039608725937200719)
      ·
        refine ⟨21987780059413088905801079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14658520039608725937200719 21987780059413088905801079)
        ·
          refine ⟨32981670089119633358701619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21987780059413088905801079 32981670089119633358701619)
          ·
            refine ⟨49472505133679450038052429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32981670089119633358701619 49472505133679450038052429)
            ·
              refine ⟨18552189425129793764269661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49472505133679450038052429 18552189425129793764269661)
              ·
                refine ⟨6957071034423672661601123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18552189425129793764269661 6957071034423672661601123)
                ·
                  refine ⟨10435606551635508992401685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6957071034423672661601123 10435606551635508992401685)
                  ·
                    refine ⟨489169057107914484018829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10435606551635508992401685 489169057107914484018829)
                    ·
                      rfl

theorem cell23_2857960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 3, 1, 6].length) (baseStart_2857960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2857960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2857960 prefixEnd_2857960 := by exact prefixLift 2857960
  have htrace : WordTrace (prefixWord ++ tailWord_2857960) baseStart_2857960 baseEnd_2857960 := by
    simpa [prefixWord, tailWord_2857960, baseEnd_2857960] using wordTrace_append hprefix tailTrace_2857960
  have hstable : (prefixWord ++ tailWord_2857960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857960).length < 2 ^ (prefixWord ++ tailWord_2857960).sum := by decide
  have hdescent : baseEnd_2857960 < baseStart_2857960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857972 : List Nat := [2, 6, 2, 1, 1, 1, 2, 3, 1, 4]
def baseStart_2857972 : Nat := 118140960795 + 2857972 * 2 ^ 59
def prefixEnd_2857972 : Nat := 4983230072969 + 3 ^ 40 * 2857972 * 2
def baseEnd_2857972 : Nat := 489171111030532468368811

theorem tailTrace_2857972 : CollatzResearch.WordTrace tailWord_2857972 prefixEnd_2857972 489171111030532468368811 := by
  unfold tailWord_2857972
  simp only [CollatzResearch.WordTrace]
  refine ⟨52119401201031510801432085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69492534934708681068576113 52119401201031510801432085)
  ·
    refine ⟨2443096931298352068817129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 52119401201031510801432085 2443096931298352068817129)
    ·
      refine ⟨1832322698473764051612847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2443096931298352068817129 1832322698473764051612847)
      ·
        refine ⟨2748484047710646077419271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1832322698473764051612847 2748484047710646077419271)
        ·
          refine ⟨4122726071565969116128907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2748484047710646077419271 4122726071565969116128907)
          ·
            refine ⟨6184089107348953674193361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4122726071565969116128907 6184089107348953674193361)
            ·
              refine ⟨4638066830511715255645021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6184089107348953674193361 4638066830511715255645021)
              ·
                refine ⟨1739275061441893220866883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4638066830511715255645021 1739275061441893220866883)
                ·
                  refine ⟨2608912592162839831300325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1739275061441893220866883 2608912592162839831300325)
                  ·
                    refine ⟨489171111030532468368811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2608912592162839831300325 489171111030532468368811)
                    ·
                      rfl

theorem cell23_2857972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_2857972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2857972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2857972 prefixEnd_2857972 := by exact prefixLift 2857972
  have htrace : WordTrace (prefixWord ++ tailWord_2857972) baseStart_2857972 baseEnd_2857972 := by
    simpa [prefixWord, tailWord_2857972, baseEnd_2857972] using wordTrace_append hprefix tailTrace_2857972
  have hstable : (prefixWord ++ tailWord_2857972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857972).length < 2 ^ (prefixWord ++ tailWord_2857972).sum := by decide
  have hdescent : baseEnd_2857972 < baseStart_2857972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857994 : List Nat := [3, 1, 2, 2, 3, 1, 3, 2, 2, 4]
def baseStart_2857994 : Nat := 118140960795 + 2857994 * 2 ^ 59
def prefixEnd_2857994 : Nat := 4983230072969 + 3 ^ 40 * 2857994 * 2
def baseEnd_2857994 : Nat := 489174876555332106343777

theorem tailTrace_2857994 : CollatzResearch.WordTrace tailWord_2857994 prefixEnd_2857994 489174876555332106343777 := by
  unfold tailWord_2857994
  simp only [CollatzResearch.WordTrace]
  refine ⟨26059901201995829840041259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69493069871988879573443357 26059901201995829840041259)
  ·
    refine ⟨39089851802993744760061889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26059901201995829840041259 39089851802993744760061889)
    ·
      refine ⟨29317388852245308570046417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39089851802993744760061889 29317388852245308570046417)
      ·
        refine ⟨21988041639183981427534813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29317388852245308570046417 21988041639183981427534813)
        ·
          refine ⟨8245515614693993035325555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21988041639183981427534813 8245515614693993035325555)
          ·
            refine ⟨12368273422040989552988333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8245515614693993035325555 12368273422040989552988333)
            ·
              refine ⟨4638102533265371082370625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12368273422040989552988333 4638102533265371082370625)
              ·
                refine ⟨3478576899949028311777969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4638102533265371082370625 3478576899949028311777969)
                ·
                  refine ⟨2608932674961771233833477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3478576899949028311777969 2608932674961771233833477)
                  ·
                    refine ⟨489174876555332106343777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2608932674961771233833477 489174876555332106343777)
                    ·
                      rfl

theorem cell23_2857994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 2, 2, 4].length) (baseStart_2857994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2857994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2857994 prefixEnd_2857994 := by exact prefixLift 2857994
  have htrace : WordTrace (prefixWord ++ tailWord_2857994) baseStart_2857994 baseEnd_2857994 := by
    simpa [prefixWord, tailWord_2857994, baseEnd_2857994] using wordTrace_append hprefix tailTrace_2857994
  have hstable : (prefixWord ++ tailWord_2857994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857994).length < 2 ^ (prefixWord ++ tailWord_2857994).sum := by decide
  have hdescent : baseEnd_2857994 < baseStart_2857994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858057 : List Nat := [1, 2, 1, 1, 2, 2, 2, 1, 5, 4, 2]
def baseStart_2858057 : Nat := 118140960795 + 2858057 * 2 ^ 59
def prefixEnd_2858057 : Nat := 4983230072969 + 3 ^ 40 * 2858057 * 2
def baseEnd_2858057 : Nat := 1467556978947229572543541

theorem tailTrace_2858057 : CollatzResearch.WordTrace tailWord_2858057 prefixEnd_2858057 1467556978947229572543541 := by
  unfold tailWord_2858057
  simp only [CollatzResearch.WordTrace]
  refine ⟨104241902606755081119708425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69494601737836720746472283 104241902606755081119708425)
  ·
    refine ⟨78181426955066310839781319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104241902606755081119708425 78181426955066310839781319)
    ·
      refine ⟨117272140432599466259671979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78181426955066310839781319 117272140432599466259671979)
      ·
        refine ⟨175908210648899199389507969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117272140432599466259671979 175908210648899199389507969)
        ·
          refine ⟨131931157986674399542130977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175908210648899199389507969 131931157986674399542130977)
          ·
            refine ⟨98948368490005799656598233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131931157986674399542130977 98948368490005799656598233)
            ·
              refine ⟨74211276367504349742448675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98948368490005799656598233 74211276367504349742448675)
              ·
                refine ⟨111316914551256524613673013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74211276367504349742448675 111316914551256524613673013)
                ·
                  refine ⟨10435960739180299182531845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 111316914551256524613673013 10435960739180299182531845)
                  ·
                    refine ⟨1956742638596306096724721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10435960739180299182531845 1956742638596306096724721)
                    ·
                      refine ⟨1467556978947229572543541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1956742638596306096724721 1467556978947229572543541)
                      ·
                        rfl

theorem cell23_2858057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 5, 4, 2].length) (baseStart_2858057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2858057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2858057 prefixEnd_2858057 := by exact prefixLift 2858057
  have htrace : WordTrace (prefixWord ++ tailWord_2858057) baseStart_2858057 baseEnd_2858057 := by
    simpa [prefixWord, tailWord_2858057, baseEnd_2858057] using wordTrace_append hprefix tailTrace_2858057
  have hstable : (prefixWord ++ tailWord_2858057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858057).length < 2 ^ (prefixWord ++ tailWord_2858057).sum := by decide
  have hdescent : baseEnd_2858057 < baseStart_2858057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858060 : List Nat := [2, 2, 1, 3, 1, 1, 1, 1, 3, 3, 5]
def baseStart_2858060 : Nat := 118140960795 + 2858060 * 2 ^ 59
def prefixEnd_2858060 : Nat := 4983230072969 + 3 ^ 40 * 2858060 * 2
def baseEnd_2858060 : Nat := 1467558519389193060806027

theorem tailTrace_2858060 : CollatzResearch.WordTrace tailWord_2858060 prefixEnd_2858060 1467558519389193060806027 := by
  unfold tailWord_2858060
  simp only [CollatzResearch.WordTrace]
  refine ⟨52121006012872106316033817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69494674683829475088045089 52121006012872106316033817)
  ·
    refine ⟨39090754509654079737025363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52121006012872106316033817 39090754509654079737025363)
    ·
      refine ⟨58636131764481119605538045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39090754509654079737025363 58636131764481119605538045)
      ·
        refine ⟨21988549411680419852076767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58636131764481119605538045 21988549411680419852076767)
        ·
          refine ⟨32982824117520629778115151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21988549411680419852076767 32982824117520629778115151)
          ·
            refine ⟨49474236176280944667172727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32982824117520629778115151 49474236176280944667172727)
            ·
              refine ⟨74211354264421417000759091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49474236176280944667172727 74211354264421417000759091)
              ·
                refine ⟨111317031396632125501138637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74211354264421417000759091 111317031396632125501138637)
                ·
                  refine ⟨41743886773737047062926989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 111317031396632125501138637 41743886773737047062926989)
                  ·
                    refine ⟨15653957540151392648597621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41743886773737047062926989 15653957540151392648597621)
                    ·
                      refine ⟨1467558519389193060806027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15653957540151392648597621 1467558519389193060806027)
                      ·
                        rfl

theorem cell23_2858060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_2858060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2858060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2858060 prefixEnd_2858060 := by exact prefixLift 2858060
  have htrace : WordTrace (prefixWord ++ tailWord_2858060) baseStart_2858060 baseEnd_2858060 := by
    simpa [prefixWord, tailWord_2858060, baseEnd_2858060] using wordTrace_append hprefix tailTrace_2858060
  have hstable : (prefixWord ++ tailWord_2858060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858060).length < 2 ^ (prefixWord ++ tailWord_2858060).sum := by decide
  have hdescent : baseEnd_2858060 < baseStart_2858060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858074 : List Nat := [3, 1, 1, 2, 1, 1, 2, 2, 6, 2, 2]
def baseStart_2858074 : Nat := 118140960795 + 2858074 * 2 ^ 59
def prefixEnd_2858074 : Nat := 4983230072969 + 3 ^ 40 * 2858074 * 2
def baseEnd_2858074 : Nat := 1467565708118356006030963

theorem tailTrace_2858074 : CollatzResearch.WordTrace tailWord_2858074 prefixEnd_2858074 1467565708118356006030963 := by
  unfold tailWord_2858074
  simp only [CollatzResearch.WordTrace]
  refine ⟨26060630661923373255769319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69495015098462328682051517 26060630661923373255769319)
  ·
    refine ⟨39090945992885059883653979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26060630661923373255769319 39090945992885059883653979)
    ·
      refine ⟨58636418989327589825480969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39090945992885059883653979 58636418989327589825480969)
      ·
        refine ⟨43977314241995692369110727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58636418989327589825480969 43977314241995692369110727)
        ·
          refine ⟨65965971362993538553666091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43977314241995692369110727 65965971362993538553666091)
          ·
            refine ⟨98948957044490307830499137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65965971362993538553666091 98948957044490307830499137)
            ·
              refine ⟨74211717783367730872874353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98948957044490307830499137 74211717783367730872874353)
              ·
                refine ⟨55658788337525798154655765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74211717783367730872874353 55658788337525798154655765)
                ·
                  refine ⟨2609005703321521788499489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 55658788337525798154655765 2609005703321521788499489)
                  ·
                    refine ⟨1956754277491141341374617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2609005703321521788499489 1956754277491141341374617)
                    ·
                      refine ⟨1467565708118356006030963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1956754277491141341374617 1467565708118356006030963)
                      ·
                        rfl

theorem cell23_2858074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 6, 2, 2].length) (baseStart_2858074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2858074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2858074 prefixEnd_2858074 := by exact prefixLift 2858074
  have htrace : WordTrace (prefixWord ++ tailWord_2858074) baseStart_2858074 baseEnd_2858074 := by
    simpa [prefixWord, tailWord_2858074, baseEnd_2858074] using wordTrace_append hprefix tailTrace_2858074
  have hstable : (prefixWord ++ tailWord_2858074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858074).length < 2 ^ (prefixWord ++ tailWord_2858074).sum := by decide
  have hdescent : baseEnd_2858074 < baseStart_2858074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858080 : List Nat := [2, 1, 1, 3, 2, 2, 2, 1, 9]
def baseStart_2858080 : Nat := 118140960795 + 2858080 * 2 ^ 59
def prefixEnd_2858080 : Nat := 4983230072969 + 3 ^ 40 * 2858080 * 2
def baseEnd_2858080 : Nat := 163063198778031442506215

theorem tailTrace_2858080 : CollatzResearch.WordTrace tailWord_2858080 prefixEnd_2858080 163063198778031442506215 := by
  unfold tailWord_2858080
  simp only [CollatzResearch.WordTrace]
  refine ⟨52121370742835878023897847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69495160990447837365197129 52121370742835878023897847)
  ·
    refine ⟨78182056114253817035846771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52121370742835878023897847 78182056114253817035846771)
    ·
      refine ⟨117273084171380725553770157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78182056114253817035846771 117273084171380725553770157)
      ·
        refine ⟨43977406564267772082663809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117273084171380725553770157 43977406564267772082663809)
        ·
          refine ⟨32983054923200829061997857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43977406564267772082663809 32983054923200829061997857)
          ·
            refine ⟨24737291192400621796498393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32983054923200829061997857 24737291192400621796498393)
            ·
              refine ⟨18552968394300466347373795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24737291192400621796498393 18552968394300466347373795)
              ·
                refine ⟨27829452591450699521060693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18552968394300466347373795 27829452591450699521060693)
                ·
                  refine ⟨163063198778031442506215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 27829452591450699521060693 163063198778031442506215)
                  ·
                    rfl

theorem cell23_2858080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 9].length) (baseStart_2858080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2858080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2858080 prefixEnd_2858080 := by exact prefixLift 2858080
  have htrace : WordTrace (prefixWord ++ tailWord_2858080) baseStart_2858080 baseEnd_2858080 := by
    simpa [prefixWord, tailWord_2858080, baseEnd_2858080] using wordTrace_append hprefix tailTrace_2858080
  have hstable : (prefixWord ++ tailWord_2858080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858080).length < 2 ^ (prefixWord ++ tailWord_2858080).sum := by decide
  have hdescent : baseEnd_2858080 < baseStart_2858080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858208 : List Nat := [2, 1, 1, 3, 1, 6, 1, 3, 1, 4]
def baseStart_2858208 : Nat := 118140960795 + 2858208 * 2 ^ 59
def prefixEnd_2858208 : Nat := 4983230072969 + 3 ^ 40 * 2858208 * 2
def baseEnd_2858208 : Nat := 489211504842019493918449

theorem tailTrace_2858208 : CollatzResearch.WordTrace tailWord_2858208 prefixEnd_2858208 489211504842019493918449 := by
  unfold tailWord_2858208
  simp only [CollatzResearch.WordTrace]
  refine ⟨52123705014604016954227639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69498273352805355938970185 52123705014604016954227639)
  ·
    refine ⟨78185557521906025431341459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52123705014604016954227639 78185557521906025431341459)
    ·
      refine ⟨117278336282859038147012189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78185557521906025431341459 117278336282859038147012189)
      ·
        refine ⟨43979376106072139305129571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117278336282859038147012189 43979376106072139305129571)
        ·
          refine ⟨65969064159108208957694357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43979376106072139305129571 65969064159108208957694357)
          ·
            refine ⟨3092299882458197294891923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 65969064159108208957694357 3092299882458197294891923)
            ·
              refine ⟨4638449823687295942337885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3092299882458197294891923 4638449823687295942337885)
              ·
                refine ⟨1739418683882735978376707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4638449823687295942337885 1739418683882735978376707)
                ·
                  refine ⟨2609128025824103967565061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1739418683882735978376707 2609128025824103967565061)
                  ·
                    refine ⟨489211504842019493918449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2609128025824103967565061 489211504842019493918449)
                    ·
                      rfl

theorem cell23_2858208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 3, 1, 4].length) (baseStart_2858208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2858208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2858208 prefixEnd_2858208 := by exact prefixLift 2858208
  have htrace : WordTrace (prefixWord ++ tailWord_2858208) baseStart_2858208 baseEnd_2858208 := by
    simpa [prefixWord, tailWord_2858208, baseEnd_2858208] using wordTrace_append hprefix tailTrace_2858208
  have hstable : (prefixWord ++ tailWord_2858208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858208).length < 2 ^ (prefixWord ++ tailWord_2858208).sum := by decide
  have hdescent : baseEnd_2858208 < baseStart_2858208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858237 : List Nat := [1, 4, 1, 1, 1, 1, 1, 1, 1, 7, 4]
def baseStart_2858237 : Nat := 118140960795 + 2858237 * 2 ^ 59
def prefixEnd_2858237 : Nat := 4983230072969 + 3 ^ 40 * 2858237 * 2
def baseEnd_2858237 : Nat := 1467649405465038868292713

theorem tailTrace_2858237 : CollatzResearch.WordTrace tailWord_2858237 prefixEnd_2858237 1467649405465038868292713 := by
  unfold tailWord_2858237
  simp only [CollatzResearch.WordTrace]
  refine ⟨104248467746102971861260965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69498978497401981240840643 104248467746102971861260965)
  ·
    refine ⟨19546587702394307223986431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104248467746102971861260965 19546587702394307223986431)
    ·
      refine ⟨29319881553591460835979647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19546587702394307223986431 29319881553591460835979647)
      ·
        refine ⟨43979822330387191253969471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29319881553591460835979647 43979822330387191253969471)
        ·
          refine ⟨65969733495580786880954207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43979822330387191253969471 65969733495580786880954207)
          ·
            refine ⟨98954600243371180321431311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65969733495580786880954207 98954600243371180321431311)
            ·
              refine ⟨148431900365056770482146967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98954600243371180321431311 148431900365056770482146967)
              ·
                refine ⟨222647850547585155723220451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148431900365056770482146967 222647850547585155723220451)
                ·
                  refine ⟨333971775821377733584830677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 222647850547585155723220451 333971775821377733584830677)
                  ·
                    refine ⟨7827463495813540630894469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 333971775821377733584830677 7827463495813540630894469)
                    ·
                      refine ⟨1467649405465038868292713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7827463495813540630894469 1467649405465038868292713)
                      ·
                        rfl

theorem cell23_2858237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 7, 4].length) (baseStart_2858237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2858237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2858237 prefixEnd_2858237 := by exact prefixLift 2858237
  have htrace : WordTrace (prefixWord ++ tailWord_2858237) baseStart_2858237 baseEnd_2858237 := by
    simpa [prefixWord, tailWord_2858237, baseEnd_2858237] using wordTrace_append hprefix tailTrace_2858237
  have hstable : (prefixWord ++ tailWord_2858237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858237).length < 2 ^ (prefixWord ++ tailWord_2858237).sum := by decide
  have hdescent : baseEnd_2858237 < baseStart_2858237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858238 : List Nat := [4, 2, 2, 1, 1, 4, 2, 1, 6]
def baseStart_2858238 : Nat := 118140960795 + 2858238 * 2 ^ 59
def prefixEnd_2858238 : Nat := 4983230072969 + 3 ^ 40 * 2858238 * 2
def baseEnd_2858238 : Nat := 163072213216188151597801

theorem tailTrace_2858238 : CollatzResearch.WordTrace tailWord_2858238 prefixEnd_2858238 163072213216188151597801 := by
  unfold tailWord_2858238
  simp only [CollatzResearch.WordTrace]
  refine ⟨13031063027387418629005921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69499002812732899354698245 13031063027387418629005921)
  ·
    refine ⟨9773297270540563971754441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13031063027387418629005921 9773297270540563971754441)
    ·
      refine ⟨7329972952905422978815831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9773297270540563971754441 7329972952905422978815831)
      ·
        refine ⟨10994959429358134468223747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7329972952905422978815831 10994959429358134468223747)
        ·
          refine ⟨16492439144037201702335621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10994959429358134468223747 16492439144037201702335621)
          ·
            refine ⟨3092332339506975319187929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16492439144037201702335621 3092332339506975319187929)
            ·
              refine ⟨2319249254630231489390947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3092332339506975319187929 2319249254630231489390947)
              ·
                refine ⟨3478873881945347234086421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2319249254630231489390947 3478873881945347234086421)
                ·
                  refine ⟨163072213216188151597801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3478873881945347234086421 163072213216188151597801)
                  ·
                    rfl

theorem cell23_2858238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 2, 1, 6].length) (baseStart_2858238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2858238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2858238 prefixEnd_2858238 := by exact prefixLift 2858238
  have htrace : WordTrace (prefixWord ++ tailWord_2858238) baseStart_2858238 baseEnd_2858238 := by
    simpa [prefixWord, tailWord_2858238, baseEnd_2858238] using wordTrace_append hprefix tailTrace_2858238
  have hstable : (prefixWord ++ tailWord_2858238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858238).length < 2 ^ (prefixWord ++ tailWord_2858238).sum := by decide
  have hdescent : baseEnd_2858238 < baseStart_2858238 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858251 : List Nat := [1, 1, 1, 1, 5, 5, 1, 2, 1, 5]
def baseStart_2858251 : Nat := 118140960795 + 2858251 * 2 ^ 59
def prefixEnd_2858251 : Nat := 4983230072969 + 3 ^ 40 * 2858251 * 2
def baseEnd_2858251 : Nat := 489218864731400604505883

theorem tailTrace_2858251 : CollatzResearch.WordTrace tailWord_2858251 prefixEnd_2858251 489218864731400604505883 := by
  unfold tailWord_2858251
  simp only [CollatzResearch.WordTrace]
  refine ⟨104248978368052252252270607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69499318912034834834847071 104248978368052252252270607)
  ·
    refine ⟨156373467552078378378405911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104248978368052252252270607 156373467552078378378405911)
    ·
      refine ⟨234560201328117567567608867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156373467552078378378405911 234560201328117567567608867)
      ·
        refine ⟨351840301992176351351413301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234560201328117567567608867 351840301992176351351413301)
        ·
          refine ⟨32985028311766532939194997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 351840301992176351351413301 32985028311766532939194997)
          ·
            refine ⟨3092346404228112463049531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32985028311766532939194997 3092346404228112463049531)
            ·
              refine ⟨4638519606342168694574297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3092346404228112463049531 4638519606342168694574297)
              ·
                refine ⟨3478889704756626520930723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4638519606342168694574297 3478889704756626520930723)
                ·
                  refine ⟨5218334557134939781396085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3478889704756626520930723 5218334557134939781396085)
                  ·
                    refine ⟨489218864731400604505883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5218334557134939781396085 489218864731400604505883)
                    ·
                      rfl

theorem cell23_2858251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 2, 1, 5].length) (baseStart_2858251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2858251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2858251 prefixEnd_2858251 := by exact prefixLift 2858251
  have htrace : WordTrace (prefixWord ++ tailWord_2858251) baseStart_2858251 baseEnd_2858251 := by
    simpa [prefixWord, tailWord_2858251, baseEnd_2858251] using wordTrace_append hprefix tailTrace_2858251
  have hstable : (prefixWord ++ tailWord_2858251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858251).length < 2 ^ (prefixWord ++ tailWord_2858251).sum := by decide
  have hdescent : baseEnd_2858251 < baseStart_2858251 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858264 : List Nat := [2, 1, 2, 3, 1, 4, 1, 2, 1, 6]
def baseStart_2858264 : Nat := 118140960795 + 2858264 * 2 ^ 59
def prefixEnd_2858264 : Nat := 4983230072969 + 3 ^ 40 * 2858264 * 2
def baseEnd_2858264 : Nat := 489221089814236754218363

theorem tailTrace_2858264 : CollatzResearch.WordTrace tailWord_2858264 prefixEnd_2858264 489221089814236754218363 := by
  unfold tailWord_2858264
  simp only [CollatzResearch.WordTrace]
  refine ⟨52124726258502577736246923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69499635011336770314995897 52124726258502577736246923)
  ·
    refine ⟨78187089387753866604370385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52124726258502577736246923 78187089387753866604370385)
    ·
      refine ⟨58640317040815399953277789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78187089387753866604370385 58640317040815399953277789)
      ·
        refine ⟨21990118890305774982479171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58640317040815399953277789 21990118890305774982479171)
        ·
          refine ⟨32985178335458662473718757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21990118890305774982479171 32985178335458662473718757)
          ·
            refine ⟨6184720937898499213822267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32985178335458662473718757 6184720937898499213822267)
            ·
              refine ⟨9277081406847748820733401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6184720937898499213822267 9277081406847748820733401)
              ·
                refine ⟨6957811055135811615550051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9277081406847748820733401 6957811055135811615550051)
                ·
                  refine ⟨10436716582703717423325077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6957811055135811615550051 10436716582703717423325077)
                  ·
                    refine ⟨489221089814236754218363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10436716582703717423325077 489221089814236754218363)
                    ·
                      rfl

theorem cell23_2858264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 2, 1, 6].length) (baseStart_2858264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2858264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2858264 prefixEnd_2858264 := by exact prefixLift 2858264
  have htrace : WordTrace (prefixWord ++ tailWord_2858264) baseStart_2858264 baseEnd_2858264 := by
    simpa [prefixWord, tailWord_2858264, baseEnd_2858264] using wordTrace_append hprefix tailTrace_2858264
  have hstable : (prefixWord ++ tailWord_2858264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858264).length < 2 ^ (prefixWord ++ tailWord_2858264).sum := by decide
  have hdescent : baseEnd_2858264 < baseStart_2858264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858277 : List Nat := [1, 3, 1, 2, 4, 12]
def baseStart_2858277 : Nat := 118140960795 + 2858277 * 2 ^ 59
def prefixEnd_2858277 : Nat := 4983230072969 + 3 ^ 40 * 2858277 * 2
def baseEnd_2858277 : Nat := 6039794011074974122603

theorem tailTrace_2858277 : CollatzResearch.WordTrace tailWord_2858277 prefixEnd_2858277 6039794011074974122603 := by
  unfold tailWord_2858277
  simp only [CollatzResearch.WordTrace]
  refine ⟨104249926665958058692717085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69499951110638705795144723 104249926665958058692717085)
  ·
    refine ⟨39093722499734272009768907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104249926665958058692717085 39093722499734272009768907)
    ·
      refine ⟨58640583749601408014653361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39093722499734272009768907 58640583749601408014653361)
      ·
        refine ⟨43980437812201056010990021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58640583749601408014653361 43980437812201056010990021)
        ·
          refine ⟨8246332089787698002060629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43980437812201056010990021 8246332089787698002060629)
          ·
            refine ⟨6039794011074974122603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 8246332089787698002060629 6039794011074974122603)
            ·
              rfl

theorem cell23_2858277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 12].length) (baseStart_2858277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2858277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2858277 prefixEnd_2858277 := by exact prefixLift 2858277
  have htrace : WordTrace (prefixWord ++ tailWord_2858277) baseStart_2858277 baseEnd_2858277 := by
    simpa [prefixWord, tailWord_2858277, baseEnd_2858277] using wordTrace_append hprefix tailTrace_2858277
  have hstable : (prefixWord ++ tailWord_2858277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858277).length < 2 ^ (prefixWord ++ tailWord_2858277).sum := by decide
  have hdescent : baseEnd_2858277 < baseStart_2858277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858282 : List Nat := [3, 1, 4, 2, 1, 1, 4, 2, 1, 1, 3]
def baseStart_2858282 : Nat := 118140960795 + 2858282 * 2 ^ 59
def prefixEnd_2858282 : Nat := 4983230072969 + 3 ^ 40 * 2858282 * 2
def baseEnd_2858282 : Nat := 1467672512094491192230007

theorem tailTrace_2858282 : CollatzResearch.WordTrace tailWord_2858282 prefixEnd_2858282 1467672512094491192230007 := by
  unfold tailWord_2858282
  simp only [CollatzResearch.WordTrace]
  refine ⟨26062527257734986136662275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69500072687293296364432733 26062527257734986136662275)
  ·
    refine ⟨39093790886602479204993413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26062527257734986136662275 39093790886602479204993413)
    ·
      refine ⟨7330085791237964850936265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39093790886602479204993413 7330085791237964850936265)
      ·
        refine ⟨5497564343428473638202199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7330085791237964850936265 5497564343428473638202199)
        ·
          refine ⟨8246346515142710457303299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5497564343428473638202199 8246346515142710457303299)
          ·
            refine ⟨12369519772714065685954949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8246346515142710457303299 12369519772714065685954949)
            ·
              refine ⟨2319284957383887316116553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12369519772714065685954949 2319284957383887316116553)
              ·
                refine ⟨1739463718037915487087415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2319284957383887316116553 1739463718037915487087415)
                ·
                  refine ⟨2609195577056873230631123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1739463718037915487087415 2609195577056873230631123)
                  ·
                    refine ⟨3913793365585309845946685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2609195577056873230631123 3913793365585309845946685)
                    ·
                      refine ⟨1467672512094491192230007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3913793365585309845946685 1467672512094491192230007)
                      ·
                        rfl

theorem cell23_2858282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_2858282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2858282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2858282 prefixEnd_2858282 := by exact prefixLift 2858282
  have htrace : WordTrace (prefixWord ++ tailWord_2858282) baseStart_2858282 baseEnd_2858282 := by
    simpa [prefixWord, tailWord_2858282, baseEnd_2858282] using wordTrace_append hprefix tailTrace_2858282
  have hstable : (prefixWord ++ tailWord_2858282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858282).length < 2 ^ (prefixWord ++ tailWord_2858282).sum := by decide
  have hdescent : baseEnd_2858282 < baseStart_2858282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858305 : List Nat := [1, 2, 5, 2, 1, 2, 1, 2, 3, 2, 2]
def baseStart_2858305 : Nat := 118140960795 + 2858305 * 2 ^ 59
def prefixEnd_2858305 : Nat := 4983230072969 + 3 ^ 40 * 2858305 * 2
def baseEnd_2858305 : Nat := 1467684322149544602242401

theorem tailTrace_2858305 : CollatzResearch.WordTrace tailWord_2858305 prefixEnd_2858305 1467684322149544602242401 := by
  unfold tailWord_2858305
  simp only [CollatzResearch.WordTrace]
  refine ⟨104250947909856619474736369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69500631939904412983157579 104250947909856619474736369)
  ·
    refine ⟨78188210932392464606052277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104250947909856619474736369 78188210932392464606052277)
    ·
      refine ⟨7330144774911793556817401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 78188210932392464606052277 7330144774911793556817401)
      ·
        refine ⟨5497608581183845167613051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7330144774911793556817401 5497608581183845167613051)
        ·
          refine ⟨8246412871775767751419577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5497608581183845167613051 8246412871775767751419577)
          ·
            refine ⟨6184809653831825813564683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8246412871775767751419577 6184809653831825813564683)
            ·
              refine ⟨9277214480747738720347025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6184809653831825813564683 9277214480747738720347025)
              ·
                refine ⟨6957910860560804040260269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9277214480747738720347025 6957910860560804040260269)
                ·
                  refine ⟨2609216572710301515097601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6957910860560804040260269 2609216572710301515097601)
                  ·
                    refine ⟨1956912429532726136323201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2609216572710301515097601 1956912429532726136323201)
                    ·
                      refine ⟨1467684322149544602242401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1956912429532726136323201 1467684322149544602242401)
                      ·
                        rfl

theorem cell23_2858305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_2858305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2858305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2858305 prefixEnd_2858305 := by exact prefixLift 2858305
  have htrace : WordTrace (prefixWord ++ tailWord_2858305) baseStart_2858305 baseEnd_2858305 := by
    simpa [prefixWord, tailWord_2858305, baseEnd_2858305] using wordTrace_append hprefix tailTrace_2858305
  have hstable : (prefixWord ++ tailWord_2858305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858305).length < 2 ^ (prefixWord ++ tailWord_2858305).sum := by decide
  have hdescent : baseEnd_2858305 < baseStart_2858305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858307 : List Nat := [1, 1, 1, 3, 1, 3, 1, 1, 4, 7]
def baseStart_2858307 : Nat := 118140960795 + 2858307 * 2 ^ 59
def prefixEnd_2858307 : Nat := 4983230072969 + 3 ^ 40 * 2858307 * 2
def baseEnd_2858307 : Nat := 489228449703617864805797

theorem tailTrace_2858307 : CollatzResearch.WordTrace tailWord_2858307 prefixEnd_2858307 489228449703617864805797 := by
  unfold tailWord_2858307
  simp only [CollatzResearch.WordTrace]
  refine ⟨104251020855849373816309175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69500680570566249210872783 104251020855849373816309175)
  ·
    refine ⟨156376531283774060724463763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104251020855849373816309175 156376531283774060724463763)
    ·
      refine ⟨234564796925661091086695645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156376531283774060724463763 234564796925661091086695645)
      ·
        refine ⟨87961798847122909157510867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 234564796925661091086695645 87961798847122909157510867)
        ·
          refine ⟨131942698270684363736266301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87961798847122909157510867 131942698270684363736266301)
          ·
            refine ⟨49478511851506636401099863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131942698270684363736266301 49478511851506636401099863)
            ·
              refine ⟨74217767777259954601649795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49478511851506636401099863 74217767777259954601649795)
              ·
                refine ⟨111326651665889931902474693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74217767777259954601649795 111326651665889931902474693)
                ·
                  refine ⟨20873747187354362231714005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 111326651665889931902474693 20873747187354362231714005)
                  ·
                    refine ⟨489228449703617864805797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20873747187354362231714005 489228449703617864805797)
                    ·
                      rfl

theorem cell23_2858307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 7].length) (baseStart_2858307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2858307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2858307 prefixEnd_2858307 := by exact prefixLift 2858307
  have htrace : WordTrace (prefixWord ++ tailWord_2858307) baseStart_2858307 baseEnd_2858307 := by
    simpa [prefixWord, tailWord_2858307, baseEnd_2858307] using wordTrace_append hprefix tailTrace_2858307
  have hstable : (prefixWord ++ tailWord_2858307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858307).length < 2 ^ (prefixWord ++ tailWord_2858307).sum := by decide
  have hdescent : baseEnd_2858307 < baseStart_2858307 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858308 : List Nat := [2, 3, 4, 1, 1, 1, 2, 1, 3, 2, 3]
def baseStart_2858308 : Nat := 118140960795 + 2858308 * 2 ^ 59
def prefixEnd_2858308 : Nat := 4983230072969 + 3 ^ 40 * 2858308 * 2
def baseEnd_2858308 : Nat := 1467685862591508090504887

theorem tailTrace_2858308 : CollatzResearch.WordTrace tailWord_2858308 prefixEnd_2858308 1467685862591508090504887 := by
  unfold tailWord_2858308
  simp only [CollatzResearch.WordTrace]
  refine ⟨52125528664422875493547789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69500704885897167324730385 52125528664422875493547789)
  ·
    refine ⟨19547073249158578310080421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52125528664422875493547789 19547073249158578310080421)
    ·
      refine ⟨3665076234217233433140079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19547073249158578310080421 3665076234217233433140079)
      ·
        refine ⟨5497614351325850149710119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3665076234217233433140079 5497614351325850149710119)
        ·
          refine ⟨8246421526988775224565179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5497614351325850149710119 8246421526988775224565179)
          ·
            refine ⟨12369632290483162836847769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8246421526988775224565179 12369632290483162836847769)
            ·
              refine ⟨9277224217862372127635827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12369632290483162836847769 9277224217862372127635827)
              ·
                refine ⟨13915836326793558191453741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9277224217862372127635827 13915836326793558191453741)
                ·
                  refine ⟨5218438622547584321795153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13915836326793558191453741 5218438622547584321795153)
                  ·
                    refine ⟨3913828966910688241346365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5218438622547584321795153 3913828966910688241346365)
                    ·
                      refine ⟨1467685862591508090504887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3913828966910688241346365 1467685862591508090504887)
                      ·
                        rfl

theorem cell23_2858308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_2858308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2858308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2858308 prefixEnd_2858308 := by exact prefixLift 2858308
  have htrace : WordTrace (prefixWord ++ tailWord_2858308) baseStart_2858308 baseEnd_2858308 := by
    simpa [prefixWord, tailWord_2858308, baseEnd_2858308] using wordTrace_append hprefix tailTrace_2858308
  have hstable : (prefixWord ++ tailWord_2858308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858308).length < 2 ^ (prefixWord ++ tailWord_2858308).sum := by decide
  have hdescent : baseEnd_2858308 < baseStart_2858308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858321 : List Nat := [1, 2, 2, 1, 4, 1, 2, 2, 4, 1, 3]
def baseStart_2858321 : Nat := 118140960795 + 2858321 * 2 ^ 59
def prefixEnd_2858321 : Nat := 4983230072969 + 3 ^ 40 * 2858321 * 2
def baseEnd_2858321 : Nat := 1467692537840016539642327

theorem tailTrace_2858321 : CollatzResearch.WordTrace tailWord_2858321 prefixEnd_2858321 1467692537840016539642327 := by
  unfold tailWord_2858321
  simp only [CollatzResearch.WordTrace]
  refine ⟨104251531477798654207318817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69501020985199102804879211 104251531477798654207318817)
  ·
    refine ⟨78188648608348990655489113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104251531477798654207318817 78188648608348990655489113)
    ·
      refine ⟨58641486456261742991616835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78188648608348990655489113 58641486456261742991616835)
      ·
        refine ⟨87962229684392614487425253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58641486456261742991616835 87962229684392614487425253)
        ·
          refine ⟨16492918065823615216392235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87962229684392614487425253 16492918065823615216392235)
          ·
            refine ⟨24739377098735422824588353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16492918065823615216392235 24739377098735422824588353)
            ·
              refine ⟨18554532824051567118441265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24739377098735422824588353 18554532824051567118441265)
              ·
                refine ⟨13915899618038675338830949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18554532824051567118441265 13915899618038675338830949)
                ·
                  refine ⟨2609231178382251626030803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13915899618038675338830949 2609231178382251626030803)
                  ·
                    refine ⟨3913846767573377439046205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2609231178382251626030803 3913846767573377439046205)
                    ·
                      refine ⟨1467692537840016539642327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3913846767573377439046205 1467692537840016539642327)
                      ·
                        rfl

theorem cell23_2858321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 4, 1, 3].length) (baseStart_2858321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2858321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2858321 prefixEnd_2858321 := by exact prefixLift 2858321
  have htrace : WordTrace (prefixWord ++ tailWord_2858321) baseStart_2858321 baseEnd_2858321 := by
    simpa [prefixWord, tailWord_2858321, baseEnd_2858321] using wordTrace_append hprefix tailTrace_2858321
  have hstable : (prefixWord ++ tailWord_2858321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858321).length < 2 ^ (prefixWord ++ tailWord_2858321).sum := by decide
  have hdescent : baseEnd_2858321 < baseStart_2858321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858325 : List Nat := [1, 3, 2, 2, 3, 3, 2, 1, 1, 2, 3]
def baseStart_2858325 : Nat := 118140960795 + 2858325 * 2 ^ 59
def prefixEnd_2858325 : Nat := 4983230072969 + 3 ^ 40 * 2858325 * 2
def baseEnd_2858325 : Nat := 1467694591762634523992309

theorem tailTrace_2858325 : CollatzResearch.WordTrace tailWord_2858325 prefixEnd_2858325 1467694591762634523992309 := by
  unfold tailWord_2858325
  simp only [CollatzResearch.WordTrace]
  refine ⟨104251677369784162890464429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69501118246522775260309619 104251677369784162890464429)
  ·
    refine ⟨39094379013669061083924161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104251677369784162890464429 39094379013669061083924161)
    ·
      refine ⟨29320784260251795812943121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39094379013669061083924161 29320784260251795812943121)
      ·
        refine ⟨21990588195188846859707341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29320784260251795812943121 21990588195188846859707341)
        ·
          refine ⟨8246470573195817572390253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21990588195188846859707341 8246470573195817572390253)
          ·
            refine ⟨3092426464948431589646345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8246470573195817572390253 3092426464948431589646345)
            ·
              refine ⟨2319319848711323692234759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3092426464948431589646345 2319319848711323692234759)
              ·
                refine ⟨3478979773066985538352139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2319319848711323692234759 3478979773066985538352139)
                ·
                  refine ⟨5218469659600478307528209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3478979773066985538352139 5218469659600478307528209)
                  ·
                    refine ⟨3913852244700358730646157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5218469659600478307528209 3913852244700358730646157)
                    ·
                      refine ⟨1467694591762634523992309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3913852244700358730646157 1467694591762634523992309)
                      ·
                        rfl

theorem cell23_2858325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 2, 1, 1, 2, 3].length) (baseStart_2858325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2858325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2858325 prefixEnd_2858325 := by exact prefixLift 2858325
  have htrace : WordTrace (prefixWord ++ tailWord_2858325) baseStart_2858325 baseEnd_2858325 := by
    simpa [prefixWord, tailWord_2858325, baseEnd_2858325] using wordTrace_append hprefix tailTrace_2858325
  have hstable : (prefixWord ++ tailWord_2858325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858325).length < 2 ^ (prefixWord ++ tailWord_2858325).sum := by decide
  have hdescent : baseEnd_2858325 < baseStart_2858325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858338 : List Nat := [3, 3, 2, 1, 1, 1, 3, 1, 4, 1, 3]
def baseStart_2858338 : Nat := 118140960795 + 2858338 * 2 ^ 59
def prefixEnd_2858338 : Nat := 4983230072969 + 3 ^ 40 * 2858338 * 2
def baseEnd_2858338 : Nat := 1467701267011142973129749

theorem tailTrace_2858338 : CollatzResearch.WordTrace tailWord_2858338 prefixEnd_2858338 1467701267011142973129749 := by
  unfold tailWord_2858338
  simp only [CollatzResearch.WordTrace]
  refine ⟨26063037879684266527671917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69501434345824710740458445 26063037879684266527671917)
  ·
    refine ⟨9773639204881599947876969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26063037879684266527671917 9773639204881599947876969)
    ·
      refine ⟨7330229403661199960907727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9773639204881599947876969 7330229403661199960907727)
      ·
        refine ⟨10995344105491799941361591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7330229403661199960907727 10995344105491799941361591)
        ·
          refine ⟨16493016158237699912042387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10995344105491799941361591 16493016158237699912042387)
          ·
            refine ⟨24739524237356549868063581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16493016158237699912042387 24739524237356549868063581)
            ·
              refine ⟨9277321589008706200523843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24739524237356549868063581 9277321589008706200523843)
              ·
                refine ⟨13915982383513059300785765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9277321589008706200523843 13915982383513059300785765)
                ·
                  refine ⟨2609246696908698618897331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13915982383513059300785765 2609246696908698618897331)
                  ·
                    refine ⟨3913870045363047928345997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2609246696908698618897331 3913870045363047928345997)
                    ·
                      refine ⟨1467701267011142973129749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3913870045363047928345997 1467701267011142973129749)
                      ·
                        rfl

theorem cell23_2858338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_2858338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2858338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2858338 prefixEnd_2858338 := by exact prefixLift 2858338
  have htrace : WordTrace (prefixWord ++ tailWord_2858338) baseStart_2858338 baseEnd_2858338 := by
    simpa [prefixWord, tailWord_2858338, baseEnd_2858338] using wordTrace_append hprefix tailTrace_2858338
  have hstable : (prefixWord ++ tailWord_2858338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858338).length < 2 ^ (prefixWord ++ tailWord_2858338).sum := by decide
  have hdescent : baseEnd_2858338 < baseStart_2858338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858354 : List Nat := [3, 2, 1, 2, 1, 2, 1, 3, 2, 6]
def baseStart_2858354 : Nat := 118140960795 + 2858354 * 2 ^ 59
def prefixEnd_2858354 : Nat := 4983230072969 + 3 ^ 40 * 2858354 * 2
def baseEnd_2858354 : Nat := 489236494233871636843225

theorem tailTrace_2858354 : CollatzResearch.WordTrace tailWord_2858354 prefixEnd_2858354 489236494233871636843225 := by
  unfold tailWord_2858354
  simp only [CollatzResearch.WordTrace]
  refine ⟨26063183771669775210817529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69501823391119400562180077 26063183771669775210817529)
  ·
    refine ⟨19547387828752331408113147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26063183771669775210817529 19547387828752331408113147)
    ·
      refine ⟨29321081743128497112169721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19547387828752331408113147 29321081743128497112169721)
      ·
        refine ⟨21990811307346372834127291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29321081743128497112169721 21990811307346372834127291)
        ·
          refine ⟨32986216961019559251190937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21990811307346372834127291 32986216961019559251190937)
          ·
            refine ⟨24739662720764669438393203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32986216961019559251190937 24739662720764669438393203)
            ·
              refine ⟨37109494081147004157589805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24739662720764669438393203 37109494081147004157589805)
              ·
                refine ⟨13916060280430126559096177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37109494081147004157589805 13916060280430126559096177)
                ·
                  refine ⟨10437045210322594919322133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13916060280430126559096177 10437045210322594919322133)
                  ·
                    refine ⟨489236494233871636843225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10437045210322594919322133 489236494233871636843225)
                    ·
                      rfl

theorem cell23_2858354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 2, 6].length) (baseStart_2858354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2858354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2858354 prefixEnd_2858354 := by exact prefixLift 2858354
  have htrace : WordTrace (prefixWord ++ tailWord_2858354) baseStart_2858354 baseEnd_2858354 := by
    simpa [prefixWord, tailWord_2858354, baseEnd_2858354] using wordTrace_append hprefix tailTrace_2858354
  have hstable : (prefixWord ++ tailWord_2858354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858354).length < 2 ^ (prefixWord ++ tailWord_2858354).sum := by decide
  have hdescent : baseEnd_2858354 < baseStart_2858354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858364 : List Nat := [2, 2, 2, 1, 1, 1, 4, 2, 2, 1, 5]
def baseStart_2858364 : Nat := 118140960795 + 2858364 * 2 ^ 59
def prefixEnd_2858364 : Nat := 4983230072969 + 3 ^ 40 * 2858364 * 2
def baseEnd_2858364 : Nat := 1467714617508159871404629

theorem tailTrace_2858364 : CollatzResearch.WordTrace tailWord_2858364 prefixEnd_2858364 1467714617508159871404629 := by
  unfold tailWord_2858364
  simp only [CollatzResearch.WordTrace]
  refine ⟨52126549908321436275567073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69502066544428581700756097 52126549908321436275567073)
  ·
    refine ⟨39094912431241077206675305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52126549908321436275567073 39094912431241077206675305)
    ·
      refine ⟨29321184323430807905006479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39094912431241077206675305 29321184323430807905006479)
      ·
        refine ⟨43981776485146211857509719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29321184323430807905006479 43981776485146211857509719)
        ·
          refine ⟨65972664727719317786264579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43981776485146211857509719 65972664727719317786264579)
          ·
            refine ⟨98958997091578976679396869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65972664727719317786264579 98958997091578976679396869)
            ·
              refine ⟨18554811954671058127386913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 98958997091578976679396869 18554811954671058127386913)
              ·
                refine ⟨13916108966003293595540185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18554811954671058127386913 13916108966003293595540185)
                ·
                  refine ⟨10437081724502470196655139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13916108966003293595540185 10437081724502470196655139)
                  ·
                    refine ⟨15655622586753705294982709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10437081724502470196655139 15655622586753705294982709)
                    ·
                      refine ⟨1467714617508159871404629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15655622586753705294982709 1467714617508159871404629)
                      ·
                        rfl

theorem cell23_2858364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 2, 1, 5].length) (baseStart_2858364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2858364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2858364 prefixEnd_2858364 := by exact prefixLift 2858364
  have htrace : WordTrace (prefixWord ++ tailWord_2858364) baseStart_2858364 baseEnd_2858364 := by
    simpa [prefixWord, tailWord_2858364, baseEnd_2858364] using wordTrace_append hprefix tailTrace_2858364
  have hstable : (prefixWord ++ tailWord_2858364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858364).length < 2 ^ (prefixWord ++ tailWord_2858364).sum := by decide
  have hdescent : baseEnd_2858364 < baseStart_2858364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858394 : List Nat := [3, 1, 1, 4, 1, 1, 1, 1, 1, 2, 7]
def baseStart_2858394 : Nat := 118140960795 + 2858394 * 2 ^ 59
def prefixEnd_2858394 : Nat := 4983230072969 + 3 ^ 40 * 2858394 * 2
def baseEnd_2858394 : Nat := 1467730021927794754029491

theorem tailTrace_2858394 : CollatzResearch.WordTrace tailWord_2858394 prefixEnd_2858394 1467730021927794754029491 := by
  unfold tailWord_2858394
  simp only [CollatzResearch.WordTrace]
  refine ⟨26063548501633546918681559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69502796004356125116484157 26063548501633546918681559)
  ·
    refine ⟨39095322752450320378022339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26063548501633546918681559 39095322752450320378022339)
    ·
      refine ⟨58642984128675480567033509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39095322752450320378022339 58642984128675480567033509)
      ·
        refine ⟨10995559524126652606318783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58642984128675480567033509 10995559524126652606318783)
        ·
          refine ⟨16493339286189978909478175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10995559524126652606318783 16493339286189978909478175)
          ·
            refine ⟨24740008929284968364217263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16493339286189978909478175 24740008929284968364217263)
            ·
              refine ⟨37110013393927452546325895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24740008929284968364217263 37110013393927452546325895)
              ·
                refine ⟨55665020090891178819488843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37110013393927452546325895 55665020090891178819488843)
                ·
                  refine ⟨83497530136336768229233265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55665020090891178819488843 83497530136336768229233265)
                  ·
                    refine ⟨62623147602252576171924949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 83497530136336768229233265 62623147602252576171924949)
                    ·
                      refine ⟨1467730021927794754029491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 62623147602252576171924949 1467730021927794754029491)
                      ·
                        rfl

theorem cell23_2858394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_2858394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2858394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2858394 prefixEnd_2858394 := by exact prefixLift 2858394
  have htrace : WordTrace (prefixWord ++ tailWord_2858394) baseStart_2858394 baseEnd_2858394 := by
    simpa [prefixWord, tailWord_2858394, baseEnd_2858394] using wordTrace_append hprefix tailTrace_2858394
  have hstable : (prefixWord ++ tailWord_2858394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858394).length < 2 ^ (prefixWord ++ tailWord_2858394).sum := by decide
  have hdescent : baseEnd_2858394 < baseStart_2858394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858452 : List Nat := [2, 4, 1, 2, 3, 2, 2, 2, 5]
def baseStart_2858452 : Nat := 118140960795 + 2858452 * 2 ^ 59
def prefixEnd_2858452 : Nat := 4983230072969 + 3 ^ 40 * 2858452 * 2
def baseEnd_2858452 : Nat := 163084422645083947456025

theorem tailTrace_2858452 : CollatzResearch.WordTrace tailWord_2858452 prefixEnd_2858452 163084422645083947456025 := by
  unfold tailWord_2858452
  simp only [CollatzResearch.WordTrace]
  refine ⟨52128154720162031790168805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69504206293549375720225073 52128154720162031790168805)
  ·
    refine ⟨9774029010030380960656651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52128154720162031790168805 9774029010030380960656651)
    ·
      refine ⟨14661043515045571440984977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9774029010030380960656651 14661043515045571440984977)
      ·
        refine ⟨10995782636284178580738733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14661043515045571440984977 10995782636284178580738733)
        ·
          refine ⟨4123418488606566967777025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10995782636284178580738733 4123418488606566967777025)
          ·
            refine ⟨3092563866454925225832769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4123418488606566967777025 3092563866454925225832769)
            ·
              refine ⟨2319422899841193919374577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3092563866454925225832769 2319422899841193919374577)
              ·
                refine ⟨1739567174880895439530933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2319422899841193919374577 1739567174880895439530933)
                ·
                  refine ⟨163084422645083947456025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1739567174880895439530933 163084422645083947456025)
                  ·
                    rfl

theorem cell23_2858452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 2, 2, 5].length) (baseStart_2858452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2858452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2858452 prefixEnd_2858452 := by exact prefixLift 2858452
  have htrace : WordTrace (prefixWord ++ tailWord_2858452) baseStart_2858452 baseEnd_2858452 := by
    simpa [prefixWord, tailWord_2858452, baseEnd_2858452] using wordTrace_append hprefix tailTrace_2858452
  have hstable : (prefixWord ++ tailWord_2858452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858452).length < 2 ^ (prefixWord ++ tailWord_2858452).sum := by decide
  have hdescent : baseEnd_2858452 < baseStart_2858452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858464 : List Nat := [2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 6]
def baseStart_2858464 : Nat := 118140960795 + 2858464 * 2 ^ 59
def prefixEnd_2858464 : Nat := 4983230072969 + 3 ^ 40 * 2858464 * 2
def baseEnd_2858464 : Nat := 1467765965573609480154169

theorem tailTrace_2858464 : CollatzResearch.WordTrace tailWord_2858464 prefixEnd_2858464 1467765965573609480154169 := by
  unfold tailWord_2858464
  simp only [CollatzResearch.WordTrace]
  refine ⟨52128373558140294814887223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69504498077520393086516297 52128373558140294814887223)
  ·
    refine ⟨78192560337210442222330835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52128373558140294814887223 78192560337210442222330835)
    ·
      refine ⟨117288840505815663333496253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78192560337210442222330835 117288840505815663333496253)
      ·
        refine ⟨43983315189680873750061095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117288840505815663333496253 43983315189680873750061095)
        ·
          refine ⟨65974972784521310625091643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43983315189680873750061095 65974972784521310625091643)
          ·
            refine ⟨98962459176781965937637465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65974972784521310625091643 98962459176781965937637465)
            ·
              refine ⟨74221844382586474453228099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98962459176781965937637465 74221844382586474453228099)
              ·
                refine ⟨111332766573879711679842149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74221844382586474453228099 111332766573879711679842149)
                ·
                  refine ⟨20874893732602445939970403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 111332766573879711679842149 20874893732602445939970403)
                  ·
                    refine ⟨31312340598903668909955605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20874893732602445939970403 31312340598903668909955605)
                    ·
                      refine ⟨1467765965573609480154169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31312340598903668909955605 1467765965573609480154169)
                      ·
                        rfl

theorem cell23_2858464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 6].length) (baseStart_2858464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2858464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2858464 prefixEnd_2858464 := by exact prefixLift 2858464
  have htrace : WordTrace (prefixWord ++ tailWord_2858464) baseStart_2858464 baseEnd_2858464 := by
    simpa [prefixWord, tailWord_2858464, baseEnd_2858464] using wordTrace_append hprefix tailTrace_2858464
  have hstable : (prefixWord ++ tailWord_2858464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858464).length < 2 ^ (prefixWord ++ tailWord_2858464).sum := by decide
  have hdescent : baseEnd_2858464 < baseStart_2858464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858478 : List Nat := [4, 1, 2, 1, 2, 1, 3, 2, 3, 4]
def baseStart_2858478 : Nat := 118140960795 + 2858478 * 2 ^ 59
def prefixEnd_2858478 : Nat := 4983230072969 + 3 ^ 40 * 2858478 * 2
def baseEnd_2858478 : Nat := 489257718100924141793035

theorem tailTrace_2858478 : CollatzResearch.WordTrace tailWord_2858478 prefixEnd_2858478 489257718100924141793035 := by
  unfold tailWord_2858478
  simp only [CollatzResearch.WordTrace]
  refine ⟨13032157217278733752598011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69504838492153246680522725 13032157217278733752598011)
  ·
    refine ⟨19548235825918100628897017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13032157217278733752598011 19548235825918100628897017)
    ·
      refine ⟨14661176869438575471672763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19548235825918100628897017 14661176869438575471672763)
      ·
        refine ⟨21991765304157863207509145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14661176869438575471672763 21991765304157863207509145)
        ·
          refine ⟨16493823978118397405631859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21991765304157863207509145 16493823978118397405631859)
          ·
            refine ⟨24740735967177596108447789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16493823978118397405631859 24740735967177596108447789)
            ·
              refine ⟨9277775987691598540667921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24740735967177596108447789 9277775987691598540667921)
              ·
                refine ⟨6958331990768698905500941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9277775987691598540667921 6958331990768698905500941)
                ·
                  refine ⟨2609374496538262089562853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6958331990768698905500941 2609374496538262089562853)
                  ·
                    refine ⟨489257718100924141793035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2609374496538262089562853 489257718100924141793035)
                    ·
                      rfl

theorem cell23_2858478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 2, 3, 4].length) (baseStart_2858478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2858478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2858478 prefixEnd_2858478 := by exact prefixLift 2858478
  have htrace : WordTrace (prefixWord ++ tailWord_2858478) baseStart_2858478 baseEnd_2858478 := by
    simpa [prefixWord, tailWord_2858478, baseEnd_2858478] using wordTrace_append hprefix tailTrace_2858478
  have hstable : (prefixWord ++ tailWord_2858478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858478).length < 2 ^ (prefixWord ++ tailWord_2858478).sum := by decide
  have hdescent : baseEnd_2858478 < baseStart_2858478 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858485 : List Nat := [1, 3, 5, 1, 1, 1, 3, 1, 2, 1, 4]
def baseStart_2858485 : Nat := 118140960795 + 2858485 * 2 ^ 59
def prefixEnd_2858485 : Nat := 4983230072969 + 3 ^ 40 * 2858485 * 2
def baseEnd_2858485 : Nat := 1467776748667353897991573

theorem tailTrace_2858485 : CollatzResearch.WordTrace tailWord_2858485 prefixEnd_2858485 1467776748667353897991573 := by
  unfold tailWord_2858485
  simp only [CollatzResearch.WordTrace]
  refine ⟨104257513049204510216288909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69505008699469673477525939 104257513049204510216288909)
  ·
    refine ⟨39096567393451691331108341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104257513049204510216288909 39096567393451691331108341)
    ·
      refine ⟨3665303193136096062291407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39096567393451691331108341 3665303193136096062291407)
      ·
        refine ⟨5497954789704144093437111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3665303193136096062291407 5497954789704144093437111)
        ·
          refine ⟨8246932184556216140155667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5497954789704144093437111 8246932184556216140155667)
          ·
            refine ⟨12370398276834324210233501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8246932184556216140155667 12370398276834324210233501)
            ·
              refine ⟨4638899353812871578837563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12370398276834324210233501 4638899353812871578837563)
              ·
                refine ⟨6958349030719307368256345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4638899353812871578837563 6958349030719307368256345)
                ·
                  refine ⟨5218761773039480526192259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6958349030719307368256345 5218761773039480526192259)
                  ·
                    refine ⟨7828142659559220789288389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5218761773039480526192259 7828142659559220789288389)
                    ·
                      refine ⟨1467776748667353897991573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7828142659559220789288389 1467776748667353897991573)
                      ·
                        rfl

theorem cell23_2858485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_2858485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2858485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2858485 prefixEnd_2858485 := by exact prefixLift 2858485
  have htrace : WordTrace (prefixWord ++ tailWord_2858485) baseStart_2858485 baseEnd_2858485 := by
    simpa [prefixWord, tailWord_2858485, baseEnd_2858485] using wordTrace_append hprefix tailTrace_2858485
  have hstable : (prefixWord ++ tailWord_2858485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858485).length < 2 ^ (prefixWord ++ tailWord_2858485).sum := by decide
  have hdescent : baseEnd_2858485 < baseStart_2858485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858488 : List Nat := [2, 1, 2, 1, 1, 5, 3, 1, 2, 2, 3]
def baseStart_2858488 : Nat := 118140960795 + 2858488 * 2 ^ 59
def prefixEnd_2858488 : Nat := 4983230072969 + 3 ^ 40 * 2858488 * 2
def baseEnd_2858488 : Nat := 1467778289109317386254059

theorem tailTrace_2858488 : CollatzResearch.WordTrace tailWord_2858488 prefixEnd_2858488 1467778289109317386254059 := by
  unfold tailWord_2858488
  simp only [CollatzResearch.WordTrace]
  refine ⟨52128811234096820864324059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69505081645462427819098745 52128811234096820864324059)
  ·
    refine ⟨78193216851145231296486089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52128811234096820864324059 78193216851145231296486089)
    ·
      refine ⟨58644912638358923472364567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78193216851145231296486089 58644912638358923472364567)
      ·
        refine ⟨87967368957538385208546851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58644912638358923472364567 87967368957538385208546851)
        ·
          refine ⟨131951053436307577812820277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87967368957538385208546851 131951053436307577812820277)
          ·
            refine ⟨12370411259653835419951901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 131951053436307577812820277 12370411259653835419951901)
            ·
              refine ⟨4638904222370188282481963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12370411259653835419951901 4638904222370188282481963)
              ·
                refine ⟨6958356333555282423722945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4638904222370188282481963 6958356333555282423722945)
                ·
                  refine ⟨5218767250166461817792209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6958356333555282423722945 5218767250166461817792209)
                  ·
                    refine ⟨3914075437624846363344157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5218767250166461817792209 3914075437624846363344157)
                    ·
                      refine ⟨1467778289109317386254059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3914075437624846363344157 1467778289109317386254059)
                      ·
                        rfl

theorem cell23_2858488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 1, 2, 2, 3].length) (baseStart_2858488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2858488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2858488 prefixEnd_2858488 := by exact prefixLift 2858488
  have htrace : WordTrace (prefixWord ++ tailWord_2858488) baseStart_2858488 baseEnd_2858488 := by
    simpa [prefixWord, tailWord_2858488, baseEnd_2858488] using wordTrace_append hprefix tailTrace_2858488
  have hstable : (prefixWord ++ tailWord_2858488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858488).length < 2 ^ (prefixWord ++ tailWord_2858488).sum := by decide
  have hdescent : baseEnd_2858488 < baseStart_2858488 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858498 : List Nat := [3, 4, 1, 2, 1, 1, 1, 1, 2, 1, 6]
def baseStart_2858498 : Nat := 118140960795 + 2858498 * 2 ^ 59
def prefixEnd_2858498 : Nat := 4983230072969 + 3 ^ 40 * 2858498 * 2
def baseEnd_2858498 : Nat := 1467783423915862347129013

theorem tailTrace_2858498 : CollatzResearch.WordTrace tailWord_2858498 prefixEnd_2858498 1467783423915862347129013 := by
  unfold tailWord_2858498
  simp only [CollatzResearch.WordTrace]
  refine ⟨26064496799539353359128037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69505324798771608957674765 26064496799539353359128037)
  ·
    refine ⟨4887093149913628754836507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26064496799539353359128037 4887093149913628754836507)
    ·
      refine ⟨7330639724870443132254761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4887093149913628754836507 7330639724870443132254761)
      ·
        refine ⟨5497979793652832349191071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7330639724870443132254761 5497979793652832349191071)
        ·
          refine ⟨8246969690479248523786607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5497979793652832349191071 8246969690479248523786607)
          ·
            refine ⟨12370454535718872785679911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8246969690479248523786607 12370454535718872785679911)
            ·
              refine ⟨18555681803578309178519867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12370454535718872785679911 18555681803578309178519867)
              ·
                refine ⟨27833522705367463767779801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18555681803578309178519867 27833522705367463767779801)
                ·
                  refine ⟨20875142029025597825834851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27833522705367463767779801 20875142029025597825834851)
                  ·
                    refine ⟨31312713043538396738752277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20875142029025597825834851 31312713043538396738752277)
                    ·
                      refine ⟨1467783423915862347129013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31312713043538396738752277 1467783423915862347129013)
                      ·
                        rfl

theorem cell23_2858498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_2858498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2858498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2858498 prefixEnd_2858498 := by exact prefixLift 2858498
  have htrace : WordTrace (prefixWord ++ tailWord_2858498) baseStart_2858498 baseEnd_2858498 := by
    simpa [prefixWord, tailWord_2858498, baseEnd_2858498] using wordTrace_append hprefix tailTrace_2858498
  have hstable : (prefixWord ++ tailWord_2858498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858498).length < 2 ^ (prefixWord ++ tailWord_2858498).sum := by decide
  have hdescent : baseEnd_2858498 < baseStart_2858498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858552 : List Nat := [2, 1, 2, 1, 4, 2, 3, 3, 1, 1, 3]
def baseStart_2858552 : Nat := 118140960795 + 2858552 * 2 ^ 59
def prefixEnd_2858552 : Nat := 4983230072969 + 3 ^ 40 * 2858552 * 2
def baseEnd_2858552 : Nat := 1467811151871205135853765

theorem tailTrace_2858552 : CollatzResearch.WordTrace tailWord_2858552 prefixEnd_2858552 1467811151871205135853765 := by
  unfold tailWord_2858552
  simp only [CollatzResearch.WordTrace]
  refine ⟨52129978369980890329488955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69506637826641187105985273 52129978369980890329488955)
  ·
    refine ⟨78194967554971335494233433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52129978369980890329488955 78194967554971335494233433)
    ·
      refine ⟨58646225666228501620675075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78194967554971335494233433 58646225666228501620675075)
      ·
        refine ⟨87969338499342752431012613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58646225666228501620675075 87969338499342752431012613)
        ·
          refine ⟨16494250968626766080814865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87969338499342752431012613 16494250968626766080814865)
          ·
            refine ⟨12370688226470074560611149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16494250968626766080814865 12370688226470074560611149)
            ·
              refine ⟨4639008084926277960229181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12370688226470074560611149 4639008084926277960229181)
              ·
                refine ⟨1739628031847354235085943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4639008084926277960229181 1739628031847354235085943)
                ·
                  refine ⟨2609442047771031352628915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1739628031847354235085943 2609442047771031352628915)
                  ·
                    refine ⟨3914163071656547028943373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2609442047771031352628915 3914163071656547028943373)
                    ·
                      refine ⟨1467811151871205135853765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3914163071656547028943373 1467811151871205135853765)
                      ·
                        rfl

theorem cell23_2858552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 3, 1, 1, 3].length) (baseStart_2858552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2858552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2858552 prefixEnd_2858552 := by exact prefixLift 2858552
  have htrace : WordTrace (prefixWord ++ tailWord_2858552) baseStart_2858552 baseEnd_2858552 := by
    simpa [prefixWord, tailWord_2858552, baseEnd_2858552] using wordTrace_append hprefix tailTrace_2858552
  have hstable : (prefixWord ++ tailWord_2858552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858552).length < 2 ^ (prefixWord ++ tailWord_2858552).sum := by decide
  have hdescent : baseEnd_2858552 < baseStart_2858552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858578 : List Nat := [3, 2, 2, 1, 2, 2, 2, 2, 1, 1, 5]
def baseStart_2858578 : Nat := 118140960795 + 2858578 * 2 ^ 59
def prefixEnd_2858578 : Nat := 4983230072969 + 3 ^ 40 * 2858578 * 2
def baseEnd_2858578 : Nat := 1467824502368222034128645

theorem tailTrace_2858578 : CollatzResearch.WordTrace tailWord_2858578 prefixEnd_2858578 1467824502368222034128645 := by
  unfold tailWord_2858578
  simp only [CollatzResearch.WordTrace]
  refine ⟨26065226259466896774856097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69507270025245058066282925 26065226259466896774856097)
  ·
    refine ⟨19548919694600172581142073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26065226259466896774856097 19548919694600172581142073)
    ·
      refine ⟨14661689770950129435856555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19548919694600172581142073 14661689770950129435856555)
      ·
        refine ⟨21992534656425194153784833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14661689770950129435856555 21992534656425194153784833)
        ·
          refine ⟨16494400992318895615338625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21992534656425194153784833 16494400992318895615338625)
          ·
            refine ⟨12370800744239171711503969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16494400992318895615338625 12370800744239171711503969)
            ·
              refine ⟨9278100558179378783627977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12370800744239171711503969 9278100558179378783627977)
              ·
                refine ⟨6958575418634534087720983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9278100558179378783627977 6958575418634534087720983)
                ·
                  refine ⟨10437863127951801131581475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6958575418634534087720983 10437863127951801131581475)
                  ·
                    refine ⟨15656794691927701697372213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10437863127951801131581475 15656794691927701697372213)
                    ·
                      refine ⟨1467824502368222034128645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15656794691927701697372213 1467824502368222034128645)
                      ·
                        rfl

theorem cell23_2858578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_2858578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2858578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2858578 prefixEnd_2858578 := by exact prefixLift 2858578
  have htrace : WordTrace (prefixWord ++ tailWord_2858578) baseStart_2858578 baseEnd_2858578 := by
    simpa [prefixWord, tailWord_2858578, baseEnd_2858578] using wordTrace_append hprefix tailTrace_2858578
  have hstable : (prefixWord ++ tailWord_2858578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858578).length < 2 ^ (prefixWord ++ tailWord_2858578).sum := by decide
  have hdescent : baseEnd_2858578 < baseStart_2858578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858588 : List Nat := [2, 2, 4, 1, 2, 1, 2, 1, 1, 1, 6]
def baseStart_2858588 : Nat := 118140960795 + 2858588 * 2 ^ 59
def prefixEnd_2858588 : Nat := 4983230072969 + 3 ^ 40 * 2858588 * 2
def baseEnd_2858588 : Nat := 1467829637174766995003599

theorem tailTrace_2858588 : CollatzResearch.WordTrace tailWord_2858588 prefixEnd_2858588 1467829637174766995003599 := by
  unfold tailWord_2858588
  simp only [CollatzResearch.WordTrace]
  refine ⟨52130634883915679403644209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69507513178554239204858945 52130634883915679403644209)
  ·
    refine ⟨39097976162936759552733157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52130634883915679403644209 39097976162936759552733157)
    ·
      refine ⟨7330870530550642416137467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39097976162936759552733157 7330870530550642416137467)
      ·
        refine ⟨10996305795825963624206201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7330870530550642416137467 10996305795825963624206201)
        ·
          refine ⟨8247229346869472718154651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10996305795825963624206201 8247229346869472718154651)
          ·
            refine ⟨12370844020304209077231977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8247229346869472718154651 12370844020304209077231977)
            ·
              refine ⟨9278133015228156807923983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12370844020304209077231977 9278133015228156807923983)
              ·
                refine ⟨13917199522842235211885975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9278133015228156807923983 13917199522842235211885975)
                ·
                  refine ⟨20875799284263352817828963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13917199522842235211885975 20875799284263352817828963)
                  ·
                    refine ⟨31313698926395029226743445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20875799284263352817828963 31313698926395029226743445)
                    ·
                      refine ⟨1467829637174766995003599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31313698926395029226743445 1467829637174766995003599)
                      ·
                        rfl

theorem cell23_2858588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_2858588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2858588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2858588 prefixEnd_2858588 := by exact prefixLift 2858588
  have htrace : WordTrace (prefixWord ++ tailWord_2858588) baseStart_2858588 baseEnd_2858588 := by
    simpa [prefixWord, tailWord_2858588, baseEnd_2858588] using wordTrace_append hprefix tailTrace_2858588
  have hstable : (prefixWord ++ tailWord_2858588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858588).length < 2 ^ (prefixWord ++ tailWord_2858588).sum := by decide
  have hdescent : baseEnd_2858588 < baseStart_2858588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858589 : List Nat := [1, 4, 4, 2, 1, 2, 1, 2, 1, 5]
def baseStart_2858589 : Nat := 118140960795 + 2858589 * 2 ^ 59
def prefixEnd_2858589 : Nat := 4983230072969 + 3 ^ 40 * 2858589 * 2
def baseEnd_2858589 : Nat := 489276716885140497030365

theorem tailTrace_2858589 : CollatzResearch.WordTrace tailWord_2858589 prefixEnd_2858589 489276716885140497030365 := by
  unfold tailWord_2858589
  simp only [CollatzResearch.WordTrace]
  refine ⟨104261306240827735978074821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69507537493885157318716547 104261306240827735978074821)
  ·
    refine ⟨19548994920155200495889029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104261306240827735978074821 19548994920155200495889029)
    ·
      refine ⟨3665436547529100092979193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19548994920155200495889029 3665436547529100092979193)
      ·
        refine ⟨2749077410646825069734395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3665436547529100092979193 2749077410646825069734395)
        ·
          refine ⟨4123616115970237604601593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2749077410646825069734395 4123616115970237604601593)
          ·
            refine ⟨3092712086977678203451195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4123616115970237604601593 3092712086977678203451195)
            ·
              refine ⟨4639068130466517305176793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3092712086977678203451195 4639068130466517305176793)
              ·
                refine ⟨3479301097849887978882595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4639068130466517305176793 3479301097849887978882595)
                ·
                  refine ⟨5218951646774831968323893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3479301097849887978882595 5218951646774831968323893)
                  ·
                    refine ⟨489276716885140497030365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5218951646774831968323893 489276716885140497030365)
                    ·
                      rfl

theorem cell23_2858589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_2858589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2858589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2858589 prefixEnd_2858589 := by exact prefixLift 2858589
  have htrace : WordTrace (prefixWord ++ tailWord_2858589) baseStart_2858589 baseEnd_2858589 := by
    simpa [prefixWord, tailWord_2858589, baseEnd_2858589] using wordTrace_append hprefix tailTrace_2858589
  have hstable : (prefixWord ++ tailWord_2858589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858589).length < 2 ^ (prefixWord ++ tailWord_2858589).sum := by decide
  have hdescent : baseEnd_2858589 < baseStart_2858589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858595 : List Nat := [1, 1, 1, 5, 1, 3, 3, 2, 1, 2, 3]
def baseStart_2858595 : Nat := 118140960795 + 2858595 * 2 ^ 59
def prefixEnd_2858595 : Nat := 4983230072969 + 3 ^ 40 * 2858595 * 2
def baseEnd_2858595 : Nat := 1467833231539348467616067

theorem tailTrace_2858595 : CollatzResearch.WordTrace tailWord_2858595 prefixEnd_2858595 1467833231539348467616067 := by
  unfold tailWord_2858595
  simp only [CollatzResearch.WordTrace]
  refine ⟨104261525078805999002793239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69507683385870666001862159 104261525078805999002793239)
  ·
    refine ⟨156392287618208998504189859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104261525078805999002793239 156392287618208998504189859)
    ·
      refine ⟨234588431427313497756284789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156392287618208998504189859 234588431427313497756284789)
      ·
        refine ⟨21992665446310640414651699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 234588431427313497756284789 21992665446310640414651699)
        ·
          refine ⟨32988998169465960621977549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21992665446310640414651699 32988998169465960621977549)
          ·
            refine ⟨12370874313549735233241581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32988998169465960621977549 12370874313549735233241581)
            ·
              refine ⟨4639077867581150712465593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12370874313549735233241581 4639077867581150712465593)
              ·
                refine ⟨3479308400685863034349195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4639077867581150712465593 3479308400685863034349195)
                ·
                  refine ⟨5218962601028794551523793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3479308400685863034349195 5218962601028794551523793)
                  ·
                    refine ⟨3914221950771595913642845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5218962601028794551523793 3914221950771595913642845)
                    ·
                      refine ⟨1467833231539348467616067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3914221950771595913642845 1467833231539348467616067)
                      ·
                        rfl

theorem cell23_2858595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 2, 1, 2, 3].length) (baseStart_2858595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2858595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2858595 prefixEnd_2858595 := by exact prefixLift 2858595
  have htrace : WordTrace (prefixWord ++ tailWord_2858595) baseStart_2858595 baseEnd_2858595 := by
    simpa [prefixWord, tailWord_2858595, baseEnd_2858595] using wordTrace_append hprefix tailTrace_2858595
  have hstable : (prefixWord ++ tailWord_2858595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858595).length < 2 ^ (prefixWord ++ tailWord_2858595).sum := by decide
  have hdescent : baseEnd_2858595 < baseStart_2858595 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858605 : List Nat := [1, 5, 1, 1, 4, 1, 1, 2, 1, 2, 4]
def baseStart_2858605 : Nat := 118140960795 + 2858605 * 2 ^ 59
def prefixEnd_2858605 : Nat := 4983230072969 + 3 ^ 40 * 2858605 * 2
def baseEnd_2858605 : Nat := 1467838366345893428491021

theorem tailTrace_2858605 : CollatzResearch.WordTrace tailWord_2858605 prefixEnd_2858605 1467838366345893428491021 := by
  unfold tailWord_2858605
  simp only [CollatzResearch.WordTrace]
  refine ⟨104261889808769770710657269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69507926539179847140438179 104261889808769770710657269)
  ·
    refine ⟨9774552169572166004124119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 104261889808769770710657269 9774552169572166004124119)
    ·
      refine ⟨14661828254358249006186179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9774552169572166004124119 14661828254358249006186179)
      ·
        refine ⟨21992742381537373509279269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14661828254358249006186179 21992742381537373509279269)
        ·
          refine ⟨4123639196538257532989863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21992742381537373509279269 4123639196538257532989863)
          ·
            refine ⟨6185458794807386299484795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4123639196538257532989863 6185458794807386299484795)
            ·
              refine ⟨9278188192211079449227193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6185458794807386299484795 9278188192211079449227193)
              ·
                refine ⟨6958641144158309586920395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9278188192211079449227193 6958641144158309586920395)
                ·
                  refine ⟨10437961716237464380380593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6958641144158309586920395 10437961716237464380380593)
                  ·
                    refine ⟨7828471287178098285285445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10437961716237464380380593 7828471287178098285285445)
                    ·
                      refine ⟨1467838366345893428491021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7828471287178098285285445 1467838366345893428491021)
                      ·
                        rfl

theorem cell23_2858605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 2, 1, 2, 4].length) (baseStart_2858605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2858605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2858605 prefixEnd_2858605 := by exact prefixLift 2858605
  have htrace : WordTrace (prefixWord ++ tailWord_2858605) baseStart_2858605 baseEnd_2858605 := by
    simpa [prefixWord, tailWord_2858605, baseEnd_2858605] using wordTrace_append hprefix tailTrace_2858605
  have hstable : (prefixWord ++ tailWord_2858605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858605).length < 2 ^ (prefixWord ++ tailWord_2858605).sum := by decide
  have hdescent : baseEnd_2858605 < baseStart_2858605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858608 : List Nat := [2, 1, 1, 1, 6, 1, 1, 1, 3, 3, 3]
def baseStart_2858608 : Nat := 118140960795 + 2858608 * 2 ^ 59
def prefixEnd_2858608 : Nat := 4983230072969 + 3 ^ 40 * 2858608 * 2
def baseEnd_2858608 : Nat := 1467839906787856916753507

theorem tailTrace_2858608 : CollatzResearch.WordTrace tailWord_2858608 prefixEnd_2858608 1467839906787856916753507 := by
  unfold tailWord_2858608
  simp only [CollatzResearch.WordTrace]
  refine ⟨52130999613879451111508239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69507999485172601482010985 52130999613879451111508239)
  ·
    refine ⟨78196499420819176667262359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52130999613879451111508239 78196499420819176667262359)
    ·
      refine ⟨117294749131228765000893539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78196499420819176667262359 117294749131228765000893539)
      ·
        refine ⟨175942123696843147501340309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117294749131228765000893539 175942123696843147501340309)
        ·
          refine ⟨8247287048289522539125327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 175942123696843147501340309 8247287048289522539125327)
          ·
            refine ⟨12370930572434283808687991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8247287048289522539125327 12370930572434283808687991)
            ·
              refine ⟨18556395858651425713031987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12370930572434283808687991 18556395858651425713031987)
              ·
                refine ⟨27834593787977138569547981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18556395858651425713031987 27834593787977138569547981)
                ·
                  refine ⟨10437972670491426963580493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27834593787977138569547981 10437972670491426963580493)
                  ·
                    refine ⟨3914239751434285111342685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10437972670491426963580493 3914239751434285111342685)
                    ·
                      refine ⟨1467839906787856916753507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3914239751434285111342685 1467839906787856916753507)
                      ·
                        rfl

theorem cell23_2858608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 3, 3, 3].length) (baseStart_2858608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2858608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2858608 prefixEnd_2858608 := by exact prefixLift 2858608
  have htrace : WordTrace (prefixWord ++ tailWord_2858608) baseStart_2858608 baseEnd_2858608 := by
    simpa [prefixWord, tailWord_2858608, baseEnd_2858608] using wordTrace_append hprefix tailTrace_2858608
  have hstable : (prefixWord ++ tailWord_2858608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858608).length < 2 ^ (prefixWord ++ tailWord_2858608).sum := by decide
  have hdescent : baseEnd_2858608 < baseStart_2858608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858632 : List Nat := [2, 1, 3, 5, 2, 1, 1, 8]
def baseStart_2858632 : Nat := 118140960795 + 2858632 * 2 ^ 59
def prefixEnd_2858632 : Nat := 4983230072969 + 3 ^ 40 * 2858632 * 2
def baseEnd_2858632 : Nat := 54364897419391289735311

theorem tailTrace_2858632 : CollatzResearch.WordTrace tailWord_2858632 prefixEnd_2858632 54364897419391289735311 := by
  unfold tailWord_2858632
  simp only [CollatzResearch.WordTrace]
  refine ⟨52131437289835977160945075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69508583053114636214593433 52131437289835977160945075)
  ·
    refine ⟨78197155934753965741417613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52131437289835977160945075 78197155934753965741417613)
    ·
      refine ⟨29323933475532737153031605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78197155934753965741417613 29323933475532737153031605)
      ·
        refine ⟨2749118763331194108096713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29323933475532737153031605 2749118763331194108096713)
        ·
          refine ⟨2061839072498395581072535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2749118763331194108096713 2061839072498395581072535)
          ·
            refine ⟨3092758608747593371608803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2061839072498395581072535 3092758608747593371608803)
            ·
              refine ⟨4639137913121390057413205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3092758608747593371608803 4639137913121390057413205)
              ·
                refine ⟨54364897419391289735311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4639137913121390057413205 54364897419391289735311)
                ·
                  rfl

theorem cell23_2858632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 8].length) (baseStart_2858632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2858632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2858632 prefixEnd_2858632 := by exact prefixLift 2858632
  have htrace : WordTrace (prefixWord ++ tailWord_2858632) baseStart_2858632 baseEnd_2858632 := by
    simpa [prefixWord, tailWord_2858632, baseEnd_2858632] using wordTrace_append hprefix tailTrace_2858632
  have hstable : (prefixWord ++ tailWord_2858632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858632).length < 2 ^ (prefixWord ++ tailWord_2858632).sum := by decide
  have hdescent : baseEnd_2858632 < baseStart_2858632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858642 : List Nat := [3, 2, 3, 1, 3, 1, 2, 1, 1, 3, 3]
def baseStart_2858642 : Nat := 118140960795 + 2858642 * 2 ^ 59
def prefixEnd_2858642 : Nat := 4983230072969 + 3 ^ 40 * 2858642 * 2
def baseEnd_2858642 : Nat := 1467857365130109783728351

theorem tailTrace_2858642 : CollatzResearch.WordTrace tailWord_2858642 prefixEnd_2858642 1467857365130109783728351 := by
  unfold tailWord_2858642
  simp only [CollatzResearch.WordTrace]
  refine ⟨26065809827408931507438545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69508826206423817353169453 26065809827408931507438545)
  ·
    refine ⟨19549357370556698630578909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26065809827408931507438545 19549357370556698630578909)
    ·
      refine ⟨7331009013958761986467091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19549357370556698630578909 7331009013958761986467091)
      ·
        refine ⟨10996513520938142979700637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7331009013958761986467091 10996513520938142979700637)
        ·
          refine ⟨4123692570351803617387739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10996513520938142979700637 4123692570351803617387739)
          ·
            refine ⟨6185538855527705426081609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4123692570351803617387739 6185538855527705426081609)
            ·
              refine ⟨4639154141645779069561207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6185538855527705426081609 4639154141645779069561207)
              ·
                refine ⟨6958731212468668604341811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4639154141645779069561207 6958731212468668604341811)
                ·
                  refine ⟨10438096818703002906512717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6958731212468668604341811 10438096818703002906512717)
                  ·
                    refine ⟨3914286307013626089942269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10438096818703002906512717 3914286307013626089942269)
                    ·
                      refine ⟨1467857365130109783728351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3914286307013626089942269 1467857365130109783728351)
                      ·
                        rfl

theorem cell23_2858642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_2858642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2858642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2858642 prefixEnd_2858642 := by exact prefixLift 2858642
  have htrace : WordTrace (prefixWord ++ tailWord_2858642) baseStart_2858642 baseEnd_2858642 := by
    simpa [prefixWord, tailWord_2858642, baseEnd_2858642] using wordTrace_append hprefix tailTrace_2858642
  have hstable : (prefixWord ++ tailWord_2858642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858642).length < 2 ^ (prefixWord ++ tailWord_2858642).sum := by decide
  have hdescent : baseEnd_2858642 < baseStart_2858642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858671 : List Nat := [1, 1, 2, 1, 2, 4, 1, 2, 9]
def baseStart_2858671 : Nat := 118140960795 + 2858671 * 2 ^ 59
def prefixEnd_2858671 : Nat := 4983230072969 + 3 ^ 40 * 2858671 * 2
def baseEnd_2858671 : Nat := 163096917341010018918413

theorem tailTrace_2858671 : CollatzResearch.WordTrace tailWord_2858671 prefixEnd_2858671 163096917341010018918413 := by
  unfold tailWord_2858671
  simp only [CollatzResearch.WordTrace]
  refine ⟨104264297026530663982559867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69509531351020442655039911 104264297026530663982559867)
  ·
    refine ⟨156396445539795995973839801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104264297026530663982559867 156396445539795995973839801)
    ·
      refine ⟨117297334154846996980379851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156396445539795995973839801 117297334154846996980379851)
      ·
        refine ⟨175946001232270495470569777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117297334154846996980379851 175946001232270495470569777)
        ·
          refine ⟨131959500924202871602927333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175946001232270495470569777 131959500924202871602927333)
          ·
            refine ⟨24742406423288038425548875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 131959500924202871602927333 24742406423288038425548875)
            ·
              refine ⟨37113609634932057638323313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24742406423288038425548875 37113609634932057638323313)
              ·
                refine ⟨27835207226199043228742485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37113609634932057638323313 27835207226199043228742485)
                ·
                  refine ⟨163096917341010018918413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 27835207226199043228742485 163096917341010018918413)
                  ·
                    rfl

theorem cell23_2858671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 9].length) (baseStart_2858671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2858671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2858671 prefixEnd_2858671 := by exact prefixLift 2858671
  have htrace : WordTrace (prefixWord ++ tailWord_2858671) baseStart_2858671 baseEnd_2858671 := by
    simpa [prefixWord, tailWord_2858671, baseEnd_2858671] using wordTrace_append hprefix tailTrace_2858671
  have hstable : (prefixWord ++ tailWord_2858671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858671).length < 2 ^ (prefixWord ++ tailWord_2858671).sum := by decide
  have hdescent : baseEnd_2858671 < baseStart_2858671 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858682 : List Nat := [3, 1, 1, 1, 2, 5, 1, 1, 4, 2, 2]
def baseStart_2858682 : Nat := 118140960795 + 2858682 * 2 ^ 59
def prefixEnd_2858682 : Nat := 4983230072969 + 3 ^ 40 * 2858682 * 2
def baseEnd_2858682 : Nat := 1467877904356289627228167

theorem tailTrace_2858682 : CollatzResearch.WordTrace tailWord_2858682 prefixEnd_2858682 1467877904356289627228167 := by
  unfold tailWord_2858682
  simp only [CollatzResearch.WordTrace]
  refine ⟨26066174557372703215302575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69509798819660541907473533 26066174557372703215302575)
  ·
    refine ⟨39099261836059054822953863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26066174557372703215302575 39099261836059054822953863)
    ·
      refine ⟨58648892754088582234430795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39099261836059054822953863 58648892754088582234430795)
      ·
        refine ⟨87973339131132873351646193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58648892754088582234430795 87973339131132873351646193)
        ·
          refine ⟨65980004348349655013734645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87973339131132873351646193 65980004348349655013734645)
          ·
            refine ⟨6185625407657780157537623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65980004348349655013734645 6185625407657780157537623)
            ·
              refine ⟨9278438111486670236306435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6185625407657780157537623 9278438111486670236306435)
              ·
                refine ⟨13917657167230005354459653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9278438111486670236306435 13917657167230005354459653)
                ·
                  refine ⟨2609560718855626003961185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13917657167230005354459653 2609560718855626003961185)
                  ·
                    refine ⟨1957170539141719502970889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2609560718855626003961185 1957170539141719502970889)
                    ·
                      refine ⟨1467877904356289627228167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1957170539141719502970889 1467877904356289627228167)
                      ·
                        rfl

theorem cell23_2858682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 4, 2, 2].length) (baseStart_2858682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2858682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2858682 prefixEnd_2858682 := by exact prefixLift 2858682
  have htrace : WordTrace (prefixWord ++ tailWord_2858682) baseStart_2858682 baseEnd_2858682 := by
    simpa [prefixWord, tailWord_2858682, baseEnd_2858682] using wordTrace_append hprefix tailTrace_2858682
  have hstable : (prefixWord ++ tailWord_2858682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858682).length < 2 ^ (prefixWord ++ tailWord_2858682).sum := by decide
  have hdescent : baseEnd_2858682 < baseStart_2858682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858688 : List Nat := [2, 1, 1, 2, 4, 1, 4, 1, 7]
def baseStart_2858688 : Nat := 118140960795 + 2858688 * 2 ^ 59
def prefixEnd_2858688 : Nat := 4983230072969 + 3 ^ 40 * 2858688 * 2
def baseEnd_2858688 : Nat := 163097887248912955972571

theorem tailTrace_2858688 : CollatzResearch.WordTrace tailWord_2858688 prefixEnd_2858688 163097887248912955972571 := by
  unfold tailWord_2858688
  simp only [CollatzResearch.WordTrace]
  refine ⟨52132458533734537942964359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69509944711646050590619145 52132458533734537942964359)
  ·
    refine ⟨78198687800601806914446539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52132458533734537942964359 78198687800601806914446539)
    ·
      refine ⟨117298031700902710371669809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78198687800601806914446539 117298031700902710371669809)
      ·
        refine ⟨87973523775677032778752357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117298031700902710371669809 87973523775677032778752357)
        ·
          refine ⟨16495035707939443646016067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87973523775677032778752357 16495035707939443646016067)
          ·
            refine ⟨24742553561909165469024101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16495035707939443646016067 24742553561909165469024101)
            ·
              refine ⟨4639228792857968525442019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24742553561909165469024101 4639228792857968525442019)
              ·
                refine ⟨6958843189286952788163029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4639228792857968525442019 6958843189286952788163029)
                ·
                  refine ⟨163097887248912955972571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6958843189286952788163029 163097887248912955972571)
                  ·
                    rfl

theorem cell23_2858688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 1, 7].length) (baseStart_2858688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2858688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2858688 prefixEnd_2858688 := by exact prefixLift 2858688
  have htrace : WordTrace (prefixWord ++ tailWord_2858688) baseStart_2858688 baseEnd_2858688 := by
    simpa [prefixWord, tailWord_2858688, baseEnd_2858688] using wordTrace_append hprefix tailTrace_2858688
  have hstable : (prefixWord ++ tailWord_2858688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858688).length < 2 ^ (prefixWord ++ tailWord_2858688).sum := by decide
  have hdescent : baseEnd_2858688 < baseStart_2858688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858750 : List Nat := [4, 2, 2, 1, 4, 1, 2, 1, 2, 2, 2]
def baseStart_2858750 : Nat := 118140960795 + 2858750 * 2 ^ 59
def prefixEnd_2858750 : Nat := 4983230072969 + 3 ^ 40 * 2858750 * 2
def baseEnd_2858750 : Nat := 1467912821040795361177855

theorem tailTrace_2858750 : CollatzResearch.WordTrace tailWord_2858750 prefixEnd_2858750 1467912821040795361177855 := by
  unfold tailWord_2858750
  simp only [CollatzResearch.WordTrace]
  refine ⟨13033397299155557559335713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69511452262162973649790469 13033397299155557559335713)
  ·
    refine ⟨9775047974366668169501785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13033397299155557559335713 9775047974366668169501785)
    ·
      refine ⟨7331285980775001127126339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9775047974366668169501785 7331285980775001127126339)
      ·
        refine ⟨10996928971162501690689509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7331285980775001127126339 10996928971162501690689509)
        ·
          refine ⟨2061924182092969067004283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10996928971162501690689509 2061924182092969067004283)
          ·
            refine ⟨3092886273139453600506425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2061924182092969067004283 3092886273139453600506425)
            ·
              refine ⟨2319664704854590200379819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3092886273139453600506425 2319664704854590200379819)
              ·
                refine ⟨3479497057281885300569729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2319664704854590200379819 3479497057281885300569729)
                ·
                  refine ⟨2609622792961413975427297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3479497057281885300569729 2609622792961413975427297)
                  ·
                    refine ⟨1957217094721060481570473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2609622792961413975427297 1957217094721060481570473)
                    ·
                      refine ⟨1467912821040795361177855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1957217094721060481570473 1467912821040795361177855)
                      ·
                        rfl

theorem cell23_2858750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 2, 1, 2, 2, 2].length) (baseStart_2858750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2858750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2858750 prefixEnd_2858750 := by exact prefixLift 2858750
  have htrace : WordTrace (prefixWord ++ tailWord_2858750) baseStart_2858750 baseEnd_2858750 := by
    simpa [prefixWord, tailWord_2858750, baseEnd_2858750] using wordTrace_append hprefix tailTrace_2858750
  have hstable : (prefixWord ++ tailWord_2858750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858750).length < 2 ^ (prefixWord ++ tailWord_2858750).sum := by decide
  have hdescent : baseEnd_2858750 < baseStart_2858750 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858755 : List Nat := [1, 1, 1, 3, 2, 2, 2, 3, 2, 4, 2]
def baseStart_2858755 : Nat := 118140960795 + 2858755 * 2 ^ 59
def prefixEnd_2858755 : Nat := 4983230072969 + 3 ^ 40 * 2858755 * 2
def baseEnd_2858755 : Nat := 1467915388444067841615331

theorem tailTrace_2858755 : CollatzResearch.WordTrace tailWord_2858755 prefixEnd_2858755 1467915388444067841615331 := by
  unfold tailWord_2858755
  simp only [CollatzResearch.WordTrace]
  refine ⟨104267360758226346328617719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69511573838817564219078479 104267360758226346328617719)
  ·
    refine ⟨156401041137339519492926579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104267360758226346328617719 156401041137339519492926579)
    ·
      refine ⟨234601561706009279239389869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156401041137339519492926579 234601561706009279239389869)
      ·
        refine ⟨87975585639753479714771201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 234601561706009279239389869 87975585639753479714771201)
        ·
          refine ⟨65981689229815109786078401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87975585639753479714771201 65981689229815109786078401)
          ·
            refine ⟨49486266922361332339558801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65981689229815109786078401 49486266922361332339558801)
            ·
              refine ⟨37114700191770999254669101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49486266922361332339558801 37114700191770999254669101)
              ·
                refine ⟨13918012571914124720500913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37114700191770999254669101 13918012571914124720500913)
                ·
                  refine ⟨10438509428935593540375685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13918012571914124720500913 10438509428935593540375685)
                  ·
                    refine ⟨1957220517925423788820441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10438509428935593540375685 1957220517925423788820441)
                    ·
                      refine ⟨1467915388444067841615331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1957220517925423788820441 1467915388444067841615331)
                      ·
                        rfl

theorem cell23_2858755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 2, 4, 2].length) (baseStart_2858755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2858755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2858755 prefixEnd_2858755 := by exact prefixLift 2858755
  have htrace : WordTrace (prefixWord ++ tailWord_2858755) baseStart_2858755 baseEnd_2858755 := by
    simpa [prefixWord, tailWord_2858755, baseEnd_2858755] using wordTrace_append hprefix tailTrace_2858755
  have hstable : (prefixWord ++ tailWord_2858755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858755).length < 2 ^ (prefixWord ++ tailWord_2858755).sum := by decide
  have hdescent : baseEnd_2858755 < baseStart_2858755 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858792 : List Nat := [2, 1, 5, 1, 1, 2, 2, 2, 2, 2, 3]
def baseStart_2858792 : Nat := 118140960795 + 2858792 * 2 ^ 59
def prefixEnd_2858792 : Nat := 4983230072969 + 3 ^ 40 * 2858792 * 2
def baseEnd_2858792 : Nat := 1467934387228284196852661

theorem tailTrace_2858792 : CollatzResearch.WordTrace tailWord_2858792 prefixEnd_2858792 1467934387228284196852661 := by
  unfold tailWord_2858792
  simp only [CollatzResearch.WordTrace]
  refine ⟨52134355129546150823857315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69512473506061534431809753 52134355129546150823857315)
  ·
    refine ⟨78201532694319226235785973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52134355129546150823857315 78201532694319226235785973)
    ·
      refine ⟨7331393690092427459604935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 78201532694319226235785973 7331393690092427459604935)
      ·
        refine ⟨10997090535138641189407403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7331393690092427459604935 10997090535138641189407403)
        ·
          refine ⟨16495635802707961784111105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10997090535138641189407403 16495635802707961784111105)
          ·
            refine ⟨12371726852030971338083329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16495635802707961784111105 12371726852030971338083329)
            ·
              refine ⟨9278795139023228503562497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12371726852030971338083329 9278795139023228503562497)
              ·
                refine ⟨6959096354267421377671873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9278795139023228503562497 6959096354267421377671873)
                ·
                  refine ⟨5219322265700566033253905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6959096354267421377671873 5219322265700566033253905)
                  ·
                    refine ⟨3914491699275424524940429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5219322265700566033253905 3914491699275424524940429)
                    ·
                      refine ⟨1467934387228284196852661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3914491699275424524940429 1467934387228284196852661)
                      ·
                        rfl

theorem cell23_2858792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_2858792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2858792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2858792 prefixEnd_2858792 := by exact prefixLift 2858792
  have htrace : WordTrace (prefixWord ++ tailWord_2858792) baseStart_2858792 baseEnd_2858792 := by
    simpa [prefixWord, tailWord_2858792, baseEnd_2858792] using wordTrace_append hprefix tailTrace_2858792
  have hstable : (prefixWord ++ tailWord_2858792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858792).length < 2 ^ (prefixWord ++ tailWord_2858792).sum := by decide
  have hdescent : baseEnd_2858792 < baseStart_2858792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858825 : List Nat := [1, 2, 1, 1, 2, 4, 2, 4, 1, 5]
def baseStart_2858825 : Nat := 118140960795 + 2858825 * 2 ^ 59
def prefixEnd_2858825 : Nat := 4983230072969 + 3 ^ 40 * 2858825 * 2
def baseEnd_2858825 : Nat := 489317110696627522580003

theorem tailTrace_2858825 : CollatzResearch.WordTrace tailWord_2858825 prefixEnd_2858825 489317110696627522580003 := by
  unfold tailWord_2858825
  simp only [CollatzResearch.WordTrace]
  refine ⟨104269913867972748283665929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69513275911981832189110619 104269913867972748283665929)
  ·
    refine ⟨78202435400979561212749447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104269913867972748283665929 78202435400979561212749447)
    ·
      refine ⟨117303653101469341819124171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78202435400979561212749447 117303653101469341819124171)
      ·
        refine ⟨175955479652204012728686257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117303653101469341819124171 175955479652204012728686257)
        ·
          refine ⟨131966609739153009546514693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175955479652204012728686257 131966609739153009546514693)
          ·
            refine ⟨24743739326091189289971505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 131966609739153009546514693 24743739326091189289971505)
            ·
              refine ⟨18557804494568391967478629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24743739326091189289971505 18557804494568391967478629)
              ·
                refine ⟨3479588342731573493902243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18557804494568391967478629 3479588342731573493902243)
                ·
                  refine ⟨5219382514097360240853365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3479588342731573493902243 5219382514097360240853365)
                  ·
                    refine ⟨489317110696627522580003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5219382514097360240853365 489317110696627522580003)
                    ·
                      rfl

theorem cell23_2858825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 4, 1, 5].length) (baseStart_2858825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2858825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2858825 prefixEnd_2858825 := by exact prefixLift 2858825
  have htrace : WordTrace (prefixWord ++ tailWord_2858825) baseStart_2858825 baseEnd_2858825 := by
    simpa [prefixWord, tailWord_2858825, baseEnd_2858825] using wordTrace_append hprefix tailTrace_2858825
  have hstable : (prefixWord ++ tailWord_2858825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858825).length < 2 ^ (prefixWord ++ tailWord_2858825).sum := by decide
  have hdescent : baseEnd_2858825 < baseStart_2858825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858865 : List Nat := [1, 2, 2, 2, 1, 3, 3, 2, 1, 1, 5]
def baseStart_2858865 : Nat := 118140960795 + 2858865 * 2 ^ 59
def prefixEnd_2858865 : Nat := 4983230072969 + 3 ^ 40 * 2858865 * 2
def baseEnd_2858865 : Nat := 1467971871316062411239825

theorem tailTrace_2858865 : CollatzResearch.WordTrace tailWord_2858865 prefixEnd_2858865 1467971871316062411239825 := by
  unfold tailWord_2858865
  simp only [CollatzResearch.WordTrace]
  refine ⟨104271372787827835115122049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69514248525218556743414699 104271372787827835115122049)
  ·
    refine ⟨78203529590870876336341537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104271372787827835115122049 78203529590870876336341537)
    ·
      refine ⟨58652647193153157252256153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78203529590870876336341537 58652647193153157252256153)
      ·
        refine ⟨43989485394864867939192115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58652647193153157252256153 43989485394864867939192115)
        ·
          refine ⟨65984228092297301908788173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43989485394864867939192115 65984228092297301908788173)
          ·
            refine ⟨24744085534611488215795565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65984228092297301908788173 24744085534611488215795565)
            ·
              refine ⟨9279032075479308080923337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24744085534611488215795565 9279032075479308080923337)
              ·
                refine ⟨6959274056609481060692503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9279032075479308080923337 6959274056609481060692503)
                ·
                  refine ⟨10438911084914221591038755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6959274056609481060692503 10438911084914221591038755)
                  ·
                    refine ⟨15658366627371332386558133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10438911084914221591038755 15658366627371332386558133)
                    ·
                      refine ⟨1467971871316062411239825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15658366627371332386558133 1467971871316062411239825)
                      ·
                        rfl

theorem cell23_2858865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 2, 1, 1, 5].length) (baseStart_2858865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2858865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2858865 prefixEnd_2858865 := by exact prefixLift 2858865
  have htrace : WordTrace (prefixWord ++ tailWord_2858865) baseStart_2858865 baseEnd_2858865 := by
    simpa [prefixWord, tailWord_2858865, baseEnd_2858865] using wordTrace_append hprefix tailTrace_2858865
  have hstable : (prefixWord ++ tailWord_2858865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858865).length < 2 ^ (prefixWord ++ tailWord_2858865).sum := by decide
  have hdescent : baseEnd_2858865 < baseStart_2858865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858890 : List Nat := [3, 1, 2, 4, 3, 1, 1, 3, 1, 1, 3]
def baseStart_2858890 : Nat := 118140960795 + 2858890 * 2 ^ 59
def prefixEnd_2858890 : Nat := 4983230072969 + 3 ^ 40 * 2858890 * 2
def baseEnd_2858890 : Nat := 1467984708332424813427211

theorem tailTrace_2858890 : CollatzResearch.WordTrace tailWord_2858890 prefixEnd_2858890 1467984708332424813427211 := by
  unfold tailWord_2858890
  simp only [CollatzResearch.WordTrace]
  refine ⟨26068071153184316096195531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69514856408491509589854749 26068071153184316096195531)
  ·
    refine ⟨39102106729776474144293297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26068071153184316096195531 39102106729776474144293297)
    ·
      refine ⟨29326580047332355608219973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39102106729776474144293297 29326580047332355608219973)
      ·
        refine ⟨5498733758874816676541245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29326580047332355608219973 5498733758874816676541245)
        ·
          refine ⟨2062025159578056253702967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5498733758874816676541245 2062025159578056253702967)
          ·
            refine ⟨3093037739367084380554451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2062025159578056253702967 3093037739367084380554451)
            ·
              refine ⟨4639556609050626570831677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3093037739367084380554451 4639556609050626570831677)
              ·
                refine ⟨1739833728393984964061879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4639556609050626570831677 1739833728393984964061879)
                ·
                  refine ⟨2609750592590977446092819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1739833728393984964061879 2609750592590977446092819)
                  ·
                    refine ⟨3914625888886466169139229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2609750592590977446092819 3914625888886466169139229)
                    ·
                      refine ⟨1467984708332424813427211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3914625888886466169139229 1467984708332424813427211)
                      ·
                        rfl

theorem cell23_2858890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_2858890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2858890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2858890 prefixEnd_2858890 := by exact prefixLift 2858890
  have htrace : WordTrace (prefixWord ++ tailWord_2858890) baseStart_2858890 baseEnd_2858890 := by
    simpa [prefixWord, tailWord_2858890, baseEnd_2858890] using wordTrace_append hprefix tailTrace_2858890
  have hstable : (prefixWord ++ tailWord_2858890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858890).length < 2 ^ (prefixWord ++ tailWord_2858890).sum := by decide
  have hdescent : baseEnd_2858890 < baseStart_2858890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858913 : List Nat := [1, 2, 3, 4, 2, 2, 1, 1, 3, 2, 2]
def baseStart_2858913 : Nat := 118140960795 + 2858913 * 2 ^ 59
def prefixEnd_2858913 : Nat := 4983230072969 + 3 ^ 40 * 2858913 * 2
def baseEnd_2858913 : Nat := 1467996518387478223439605

theorem tailTrace_2858913 : CollatzResearch.WordTrace tailWord_2858913 prefixEnd_2858913 1467996518387478223439605 := by
  unfold tailWord_2858913
  simp only [CollatzResearch.WordTrace]
  refine ⟨104273123491653939312869393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69515415661102626208579595 104273123491653939312869393)
  ·
    refine ⟨78204842618740454484652045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104273123491653939312869393 78204842618740454484652045)
    ·
      refine ⟨29326815982027670431744517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78204842618740454484652045 29326815982027670431744517)
      ·
        refine ⟨5498777996630188205952097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29326815982027670431744517 5498777996630188205952097)
        ·
          refine ⟨4124083497472641154464073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5498777996630188205952097 4124083497472641154464073)
          ·
            refine ⟨3093062623104480865848055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4124083497472641154464073 3093062623104480865848055)
            ·
              refine ⟨4639593934656721298772083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3093062623104480865848055 4639593934656721298772083)
              ·
                refine ⟨6959390901985081948158125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4639593934656721298772083 6959390901985081948158125)
                ·
                  refine ⟨2609771588244405730559297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6959390901985081948158125 2609771588244405730559297)
                  ·
                    refine ⟨1957328691183304297919473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2609771588244405730559297 1957328691183304297919473)
                    ·
                      refine ⟨1467996518387478223439605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1957328691183304297919473 1467996518387478223439605)
                      ·
                        rfl

theorem cell23_2858913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_2858913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2858913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2858913 prefixEnd_2858913 := by exact prefixLift 2858913
  have htrace : WordTrace (prefixWord ++ tailWord_2858913) baseStart_2858913 baseEnd_2858913 := by
    simpa [prefixWord, tailWord_2858913, baseEnd_2858913] using wordTrace_append hprefix tailTrace_2858913
  have hstable : (prefixWord ++ tailWord_2858913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858913).length < 2 ^ (prefixWord ++ tailWord_2858913).sum := by decide
  have hdescent : baseEnd_2858913 < baseStart_2858913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858955 : List Nat := [1, 1, 1, 1, 3, 4, 1, 3, 2, 1, 5]
def baseStart_2858955 : Nat := 118140960795 + 2858955 * 2 ^ 59
def prefixEnd_2858955 : Nat := 4983230072969 + 3 ^ 40 * 2858955 * 2
def baseEnd_2858955 : Nat := 1468018084574967059114411

theorem tailTrace_2858955 : CollatzResearch.WordTrace tailWord_2858955 prefixEnd_2858955 1468018084574967059114411 := by
  unfold tailWord_2858955
  simp only [CollatzResearch.WordTrace]
  refine ⟨104274655357501780485898319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69516436905001186990598879 104274655357501780485898319)
  ·
    refine ⟨156411983036252670728847479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104274655357501780485898319 156411983036252670728847479)
    ·
      refine ⟨234617974554379006093271219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156411983036252670728847479 234617974554379006093271219)
      ·
        refine ⟨351926961831568509139906829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234617974554379006093271219 351926961831568509139906829)
        ·
          refine ⟨131972610686838190927465061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 351926961831568509139906829 131972610686838190927465061)
          ·
            refine ⟨24744864503782160798899699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 131972610686838190927465061 24744864503782160798899699)
            ·
              refine ⟨37117296755673241198349549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24744864503782160798899699 37117296755673241198349549)
              ·
                refine ⟨13918986283377465449381081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37117296755673241198349549 13918986283377465449381081)
                ·
                  refine ⟨10439239712533099087035811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13918986283377465449381081 10439239712533099087035811)
                  ·
                    refine ⟨15658859568799648630553717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10439239712533099087035811 15658859568799648630553717)
                    ·
                      refine ⟨1468018084574967059114411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15658859568799648630553717 1468018084574967059114411)
                      ·
                        rfl

theorem cell23_2858955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 2, 1, 5].length) (baseStart_2858955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2858955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2858955 prefixEnd_2858955 := by exact prefixLift 2858955
  have htrace : WordTrace (prefixWord ++ tailWord_2858955) baseStart_2858955 baseEnd_2858955 := by
    simpa [prefixWord, tailWord_2858955, baseEnd_2858955] using wordTrace_append hprefix tailTrace_2858955
  have hstable : (prefixWord ++ tailWord_2858955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858955).length < 2 ^ (prefixWord ++ tailWord_2858955).sum := by decide
  have hdescent : baseEnd_2858955 < baseStart_2858955 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2858986 : List Nat := [3, 1, 3, 1, 2, 1, 1, 5, 2, 2, 2]
def baseStart_2858986 : Nat := 118140960795 + 2858986 * 2 ^ 59
def prefixEnd_2858986 : Nat := 4983230072969 + 3 ^ 40 * 2858986 * 2
def baseEnd_2858986 : Nat := 1468034002475256437826769

theorem tailTrace_2858986 : CollatzResearch.WordTrace tailWord_2858986 prefixEnd_2858986 1468034002475256437826769 := by
  unfold tailWord_2858986
  simp only [CollatzResearch.WordTrace]
  refine ⟨26068946505097368195069203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69517190680259648520184541 26068946505097368195069203)
  ·
    refine ⟨39103419757646052292603805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26068946505097368195069203 39103419757646052292603805)
    ·
      refine ⟨14663782409117269609726427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39103419757646052292603805 14663782409117269609726427)
      ·
        refine ⟨21995673613675904414589641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14663782409117269609726427 21995673613675904414589641)
        ·
          refine ⟨16496755210256928310942231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21995673613675904414589641 16496755210256928310942231)
          ·
            refine ⟨24745132815385392466413347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16496755210256928310942231 24745132815385392466413347)
            ·
              refine ⟨37117699223078088699620021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24745132815385392466413347 37117699223078088699620021)
              ·
                refine ⟨3479784302163570815589377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37117699223078088699620021 3479784302163570815589377)
                ·
                  refine ⟨2609838226622678111692033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3479784302163570815589377 2609838226622678111692033)
                  ·
                    refine ⟨1957378669967008583769025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2609838226622678111692033 1957378669967008583769025)
                    ·
                      refine ⟨1468034002475256437826769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1957378669967008583769025 1468034002475256437826769)
                      ·
                        rfl

theorem cell23_2858986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 5, 2, 2, 2].length) (baseStart_2858986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2858986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2858986 prefixEnd_2858986 := by exact prefixLift 2858986
  have htrace : WordTrace (prefixWord ++ tailWord_2858986) baseStart_2858986 baseEnd_2858986 := by
    simpa [prefixWord, tailWord_2858986, baseEnd_2858986] using wordTrace_append hprefix tailTrace_2858986
  have hstable : (prefixWord ++ tailWord_2858986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2858986).length < 2 ^ (prefixWord ++ tailWord_2858986).sum := by decide
  have hdescent : baseEnd_2858986 < baseStart_2858986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2858986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859009 : List Nat := [1, 2, 4, 1, 2, 1, 4, 3, 5]
def baseStart_2859009 : Nat := 118140960795 + 2859009 * 2 ^ 59
def prefixEnd_2859009 : Nat := 4983230072969 + 3 ^ 40 * 2859009 * 2
def baseEnd_2859009 : Nat := 163116201392256649759907

theorem tailTrace_2859009 : CollatzResearch.WordTrace tailWord_2859009 prefixEnd_2859009 163116201392256649759907 := by
  unfold tailWord_2859009
  simp only [CollatzResearch.WordTrace]
  refine ⟨104276624899306147708364081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69517749932870765138909387 104276624899306147708364081)
  ·
    refine ⟨78207468674479610781273061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104276624899306147708364081 78207468674479610781273061)
    ·
      refine ⟨14663900376464927021488699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78207468674479610781273061 14663900376464927021488699)
      ·
        refine ⟨21995850564697390532233049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14663900376464927021488699 21995850564697390532233049)
        ·
          refine ⟨16496887923523042899174787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21995850564697390532233049 16496887923523042899174787)
          ·
            refine ⟨24745331885284564348762181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16496887923523042899174787 24745331885284564348762181)
            ·
              refine ⟨4639749728490855815392909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24745331885284564348762181 4639749728490855815392909)
              ·
                refine ⟨1739906148184070930772341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4639749728490855815392909 1739906148184070930772341)
                ·
                  refine ⟨163116201392256649759907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1739906148184070930772341 163116201392256649759907)
                  ·
                    rfl

theorem cell23_2859009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 3, 5].length) (baseStart_2859009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2859009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2859009 prefixEnd_2859009 := by exact prefixLift 2859009
  have htrace : WordTrace (prefixWord ++ tailWord_2859009) baseStart_2859009 baseEnd_2859009 := by
    simpa [prefixWord, tailWord_2859009, baseEnd_2859009] using wordTrace_append hprefix tailTrace_2859009
  have hstable : (prefixWord ++ tailWord_2859009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859009).length < 2 ^ (prefixWord ++ tailWord_2859009).sum := by decide
  have hdescent : baseEnd_2859009 < baseStart_2859009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859014 : List Nat := [6, 2, 1, 2, 1, 2, 1, 2, 2, 1, 3]
def baseStart_2859014 : Nat := 118140960795 + 2859014 * 2 ^ 59
def prefixEnd_2859014 : Nat := 4983230072969 + 3 ^ 40 * 2859014 * 2
def baseEnd_2859014 : Nat := 1468048379933582328276641

theorem tailTrace_2859014 : CollatzResearch.WordTrace tailWord_2859014 prefixEnd_2859014 1468048379933582328276641 := by
  unfold tailWord_2859014
  simp only [CollatzResearch.WordTrace]
  refine ⟨3258650227009001048821753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 69517871509525355708197397 3258650227009001048821753)
  ·
    refine ⟨2443987670256750786616315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3258650227009001048821753 2443987670256750786616315)
    ·
      refine ⟨3665981505385126179924473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2443987670256750786616315 3665981505385126179924473)
      ·
        refine ⟨2749486129038844634943355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3665981505385126179924473 2749486129038844634943355)
        ·
          refine ⟨4124229193558266952415033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2749486129038844634943355 4124229193558266952415033)
          ·
            refine ⟨3093171895168700214311275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4124229193558266952415033 3093171895168700214311275)
            ·
              refine ⟨4639757842753050321466913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3093171895168700214311275 4639757842753050321466913)
              ·
                refine ⟨3479818382064787741100185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4639757842753050321466913 3479818382064787741100185)
                ·
                  refine ⟨2609863786548590805825139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3479818382064787741100185 2609863786548590805825139)
                  ·
                    refine ⟨3914795679822886208737709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2609863786548590805825139 3914795679822886208737709)
                    ·
                      refine ⟨1468048379933582328276641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3914795679822886208737709 1468048379933582328276641)
                      ·
                        rfl

theorem cell23_2859014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_2859014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2859014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2859014 prefixEnd_2859014 := by exact prefixLift 2859014
  have htrace : WordTrace (prefixWord ++ tailWord_2859014) baseStart_2859014 baseEnd_2859014 := by
    simpa [prefixWord, tailWord_2859014, baseEnd_2859014] using wordTrace_append hprefix tailTrace_2859014
  have hstable : (prefixWord ++ tailWord_2859014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859014).length < 2 ^ (prefixWord ++ tailWord_2859014).sum := by decide
  have hdescent : baseEnd_2859014 < baseStart_2859014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859022 : List Nat := [4, 1, 1, 2, 2, 1, 2, 1, 4, 5]
def baseStart_2859022 : Nat := 118140960795 + 2859022 * 2 ^ 59
def prefixEnd_2859022 : Nat := 4983230072969 + 3 ^ 40 * 2859022 * 2
def baseEnd_2859022 : Nat := 489350829259606098992201

theorem tailTrace_2859022 : CollatzResearch.WordTrace tailWord_2859022 prefixEnd_2859022 489350829259606098992201 := by
  unfold tailWord_2859022
  simp only [CollatzResearch.WordTrace]
  refine ⟨13034637381032381366073415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69518066032172700619058213 13034637381032381366073415)
  ·
    refine ⟨19551956071548572049110123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13034637381032381366073415 19551956071548572049110123)
    ·
      refine ⟨29327934107322858073665185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19551956071548572049110123 29327934107322858073665185)
      ·
        refine ⟨21995950580492143555248889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29327934107322858073665185 21995950580492143555248889)
        ·
          refine ⟨16496962935369107666436667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21995950580492143555248889 16496962935369107666436667)
          ·
            refine ⟨24745444403053661499655001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16496962935369107666436667 24745444403053661499655001)
            ·
              refine ⟨18559083302290246124741251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24745444403053661499655001 18559083302290246124741251)
              ·
                refine ⟨27838624953435369187111877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18559083302290246124741251 27838624953435369187111877)
                ·
                  refine ⟨5219742178769131722583477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27838624953435369187111877 5219742178769131722583477)
                  ·
                    refine ⟨489350829259606098992201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5219742178769131722583477 489350829259606098992201)
                    ·
                      rfl

theorem cell23_2859022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 4, 5].length) (baseStart_2859022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2859022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2859022 prefixEnd_2859022 := by exact prefixLift 2859022
  have htrace : WordTrace (prefixWord ++ tailWord_2859022) baseStart_2859022 baseEnd_2859022 := by
    simpa [prefixWord, tailWord_2859022, baseEnd_2859022] using wordTrace_append hprefix tailTrace_2859022
  have hstable : (prefixWord ++ tailWord_2859022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859022).length < 2 ^ (prefixWord ++ tailWord_2859022).sum := by decide
  have hdescent : baseEnd_2859022 < baseStart_2859022 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859042 : List Nat := [3, 3, 1, 1, 1, 2, 1, 1, 3, 3, 4]
def baseStart_2859042 : Nat := 118140960795 + 2859042 * 2 ^ 59
def prefixEnd_2859042 : Nat := 4983230072969 + 3 ^ 40 * 2859042 * 2
def baseEnd_2859042 : Nat := 1468062757391908218726511

theorem tailTrace_2859042 : CollatzResearch.WordTrace tailWord_2859042 prefixEnd_2859042 1468062757391908218726511 := by
  unfold tailWord_2859042
  simp only [CollatzResearch.WordTrace]
  refine ⟨26069457127046648586078845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69518552338791062896210253 26069457127046648586078845)
  ·
    refine ⟨9776046422642493219779567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26069457127046648586078845 9776046422642493219779567)
    ·
      refine ⟨14664069633963739829669351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9776046422642493219779567 14664069633963739829669351)
      ·
        refine ⟨21996104450945609744504027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14664069633963739829669351 21996104450945609744504027)
        ·
          refine ⟨32994156676418414616756041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21996104450945609744504027 32994156676418414616756041)
          ·
            refine ⟨24745617507313810962567031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32994156676418414616756041 24745617507313810962567031)
            ·
              refine ⟨37118426260970716443850547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24745617507313810962567031 37118426260970716443850547)
              ·
                refine ⟨55677639391456074665775821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37118426260970716443850547 55677639391456074665775821)
                ·
                  refine ⟨20879114771796027999665933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55677639391456074665775821 20879114771796027999665933)
                  ·
                    refine ⟨7829668039423510499874725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20879114771796027999665933 7829668039423510499874725)
                    ·
                      refine ⟨1468062757391908218726511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7829668039423510499874725 1468062757391908218726511)
                      ·
                        rfl

theorem cell23_2859042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_2859042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2859042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2859042 prefixEnd_2859042 := by exact prefixLift 2859042
  have htrace : WordTrace (prefixWord ++ tailWord_2859042) baseStart_2859042 baseEnd_2859042 := by
    simpa [prefixWord, tailWord_2859042, baseEnd_2859042] using wordTrace_append hprefix tailTrace_2859042
  have hstable : (prefixWord ++ tailWord_2859042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859042).length < 2 ^ (prefixWord ++ tailWord_2859042).sum := by decide
  have hdescent : baseEnd_2859042 < baseStart_2859042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859052 : List Nat := [2, 2, 1, 1, 1, 2, 2, 3, 5, 4]
def baseStart_2859052 : Nat := 118140960795 + 2859052 * 2 ^ 59
def prefixEnd_2859052 : Nat := 4983230072969 + 3 ^ 40 * 2859052 * 2
def baseEnd_2859052 : Nat := 489355964066151059867155

theorem tailTrace_2859052 : CollatzResearch.WordTrace tailWord_2859052 prefixEnd_2859052 489355964066151059867155 := by
  unfold tailWord_2859052
  simp only [CollatzResearch.WordTrace]
  refine ⟨52139096619075183026089705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69518795492100244034786273 52139096619075183026089705)
  ·
    refine ⟨39104322464306387269567279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52139096619075183026089705 39104322464306387269567279)
    ·
      refine ⟨58656483696459580904350919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39104322464306387269567279 58656483696459580904350919)
      ·
        refine ⟨87984725544689371356526379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58656483696459580904350919 87984725544689371356526379)
        ·
          refine ⟨131977088317034057034789569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87984725544689371356526379 131977088317034057034789569)
          ·
            refine ⟨98982816237775542776092177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131977088317034057034789569 98982816237775542776092177)
            ·
              refine ⟨74237112178331657082069133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98982816237775542776092177 74237112178331657082069133)
              ·
                refine ⟨27838917066874371405775925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74237112178331657082069133 27838917066874371405775925)
                ·
                  refine ⟨2609898475019472319291493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27838917066874371405775925 2609898475019472319291493)
                  ·
                    refine ⟨489355964066151059867155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2609898475019472319291493 489355964066151059867155)
                    ·
                      rfl

theorem cell23_2859052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 4].length) (baseStart_2859052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2859052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2859052 prefixEnd_2859052 := by exact prefixLift 2859052
  have htrace : WordTrace (prefixWord ++ tailWord_2859052) baseStart_2859052 baseEnd_2859052 := by
    simpa [prefixWord, tailWord_2859052, baseEnd_2859052] using wordTrace_append hprefix tailTrace_2859052
  have hstable : (prefixWord ++ tailWord_2859052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859052).length < 2 ^ (prefixWord ++ tailWord_2859052).sum := by decide
  have hdescent : baseEnd_2859052 < baseStart_2859052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859055 : List Nat := [1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 6]
def baseStart_2859055 : Nat := 118140960795 + 2859055 * 2 ^ 59
def prefixEnd_2859055 : Nat := 4983230072969 + 3 ^ 40 * 2859055 * 2
def baseEnd_2859055 : Nat := 1468069432640416667863951

theorem tailTrace_2859055 : CollatzResearch.WordTrace tailWord_2859055 prefixEnd_2859055 1468069432640416667863951 := by
  unfold tailWord_2859055
  simp only [CollatzResearch.WordTrace]
  refine ⟨104278302657139497564538619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69518868438092998376359079 104278302657139497564538619)
  ·
    refine ⟨156417453985709246346807929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104278302657139497564538619 156417453985709246346807929)
    ·
      refine ⟨117313090489281934760105947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156417453985709246346807929 117313090489281934760105947)
      ·
        refine ⟨175969635733922902140158921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117313090489281934760105947 175969635733922902140158921)
        ·
          refine ⟨131977226800442176605119191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175969635733922902140158921 131977226800442176605119191)
          ·
            refine ⟨197965840200663264907678787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131977226800442176605119191 197965840200663264907678787)
            ·
              refine ⟨296948760300994897361518181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197965840200663264907678787 296948760300994897361518181)
              ·
                refine ⟨55677892556436543255284659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 296948760300994897361518181 55677892556436543255284659)
                ·
                  refine ⟨83516838834654814882926989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55677892556436543255284659 83516838834654814882926989)
                  ·
                    refine ⟨31318814562995555581097621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 83516838834654814882926989 31318814562995555581097621)
                    ·
                      refine ⟨1468069432640416667863951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31318814562995555581097621 1468069432640416667863951)
                      ·
                        rfl

theorem cell23_2859055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 6].length) (baseStart_2859055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2859055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2859055 prefixEnd_2859055 := by exact prefixLift 2859055
  have htrace : WordTrace (prefixWord ++ tailWord_2859055) baseStart_2859055 baseEnd_2859055 := by
    simpa [prefixWord, tailWord_2859055, baseEnd_2859055] using wordTrace_append hprefix tailTrace_2859055
  have hstable : (prefixWord ++ tailWord_2859055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859055).length < 2 ^ (prefixWord ++ tailWord_2859055).sum := by decide
  have hdescent : baseEnd_2859055 < baseStart_2859055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859060 : List Nat := [2, 5, 1, 2, 3, 1, 1, 3, 5]
def baseStart_2859060 : Nat := 118140960795 + 2859060 * 2 ^ 59
def prefixEnd_2859060 : Nat := 4983230072969 + 3 ^ 40 * 2859060 * 2
def baseEnd_2859060 : Nat := 163119111115965460922381

theorem tailTrace_2859060 : CollatzResearch.WordTrace tailWord_2859060 prefixEnd_2859060 163119111115965460922381 := by
  unfold tailWord_2859060
  simp only [CollatzResearch.WordTrace]
  refine ⟨52139242511060691709235317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69518990014747588945647089 52139242511060691709235317)
  ·
    refine ⟨4888053985411939847740811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52139242511060691709235317 4888053985411939847740811)
    ·
      refine ⟨7332080978117909771611217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4888053985411939847740811 7332080978117909771611217)
      ·
        refine ⟨5499060733588432328708413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7332080978117909771611217 5499060733588432328708413)
        ·
          refine ⟨2062147775095662123265655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5499060733588432328708413 2062147775095662123265655)
          ·
            refine ⟨3093221662643493184898483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2062147775095662123265655 3093221662643493184898483)
            ·
              refine ⟨4639832493965239777347725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3093221662643493184898483 4639832493965239777347725)
              ·
                refine ⟨1739937185236964916505397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4639832493965239777347725 1739937185236964916505397)
                ·
                  refine ⟨163119111115965460922381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1739937185236964916505397 163119111115965460922381)
                  ·
                    rfl

theorem cell23_2859060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 3, 5].length) (baseStart_2859060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2859060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2859060 prefixEnd_2859060 := by exact prefixLift 2859060
  have htrace : WordTrace (prefixWord ++ tailWord_2859060) baseStart_2859060 baseEnd_2859060 := by
    simpa [prefixWord, tailWord_2859060, baseEnd_2859060] using wordTrace_append hprefix tailTrace_2859060
  have hstable : (prefixWord ++ tailWord_2859060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859060).length < 2 ^ (prefixWord ++ tailWord_2859060).sum := by decide
  have hdescent : baseEnd_2859060 < baseStart_2859060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859079 : List Nat := [1, 1, 4, 1, 3, 1, 3, 2, 2, 2, 3]
def baseStart_2859079 : Nat := 118140960795 + 2859079 * 2 ^ 59
def prefixEnd_2859079 : Nat := 4983230072969 + 3 ^ 40 * 2859079 * 2
def baseEnd_2859079 : Nat := 1468081756176124573963841

theorem tailTrace_2859079 : CollatzResearch.WordTrace tailWord_2859079 prefixEnd_2859079 1468081756176124573963841 := by
  unfold tailWord_2859079
  simp only [CollatzResearch.WordTrace]
  refine ⟨104279178009052549663412291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69519452006035033108941527 104279178009052549663412291)
  ·
    refine ⟨156418767013578824495118437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104279178009052549663412291 156418767013578824495118437)
    ·
      refine ⟨29328518815046029592834707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 156418767013578824495118437 29328518815046029592834707)
      ·
        refine ⟨43992778222569044389252061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29328518815046029592834707 43992778222569044389252061)
        ·
          refine ⟨16497291833463391645969523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43992778222569044389252061 16497291833463391645969523)
          ·
            refine ⟨24745937750195087468954285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16497291833463391645969523 24745937750195087468954285)
            ·
              refine ⟨9279726656323157800857857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24745937750195087468954285 9279726656323157800857857)
              ·
                refine ⟨6959794992242368350643393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9279726656323157800857857 6959794992242368350643393)
                ·
                  refine ⟨5219846244181776262982545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6959794992242368350643393 5219846244181776262982545)
                  ·
                    refine ⟨3914884683136332197236909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5219846244181776262982545 3914884683136332197236909)
                    ·
                      refine ⟨1468081756176124573963841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3914884683136332197236909 1468081756176124573963841)
                      ·
                        rfl

theorem cell23_2859079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 2, 2, 2, 3].length) (baseStart_2859079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2859079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2859079 prefixEnd_2859079 := by exact prefixLift 2859079
  have htrace : WordTrace (prefixWord ++ tailWord_2859079) baseStart_2859079 baseEnd_2859079 := by
    simpa [prefixWord, tailWord_2859079, baseEnd_2859079] using wordTrace_append hprefix tailTrace_2859079
  have hstable : (prefixWord ++ tailWord_2859079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859079).length < 2 ^ (prefixWord ++ tailWord_2859079).sum := by decide
  have hdescent : baseEnd_2859079 < baseStart_2859079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859082 : List Nat := [3, 1, 2, 1, 1, 2, 1, 6, 6]
def baseStart_2859082 : Nat := 118140960795 + 2859082 * 2 ^ 59
def prefixEnd_2859082 : Nat := 4983230072969 + 3 ^ 40 * 2859082 * 2
def baseEnd_2859082 : Nat := 163120366290898673580703

theorem tailTrace_2859082 : CollatzResearch.WordTrace tailWord_2859082 prefixEnd_2859082 163120366290898673580703 := by
  unfold tailWord_2859082
  simp only [CollatzResearch.WordTrace]
  refine ⟨26069821857010420293942875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69519524952027787450514333 26069821857010420293942875)
  ·
    refine ⟨39104732785515630440914313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26069821857010420293942875 39104732785515630440914313)
    ·
      refine ⟨29328549589136722830685735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39104732785515630440914313 29328549589136722830685735)
      ·
        refine ⟨43992824383705084246028603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29328549589136722830685735 43992824383705084246028603)
        ·
          refine ⟨65989236575557626369042905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43992824383705084246028603 65989236575557626369042905)
          ·
            refine ⟨49491927431668219776782179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65989236575557626369042905 49491927431668219776782179)
            ·
              refine ⟨74237891147502329665173269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49491927431668219776782179 74237891147502329665173269)
              ·
                refine ⟨3479901147539171703054997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 74237891147502329665173269 3479901147539171703054997)
                ·
                  refine ⟨163120366290898673580703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3479901147539171703054997 163120366290898673580703)
                  ·
                    rfl

theorem cell23_2859082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 6, 6].length) (baseStart_2859082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2859082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2859082 prefixEnd_2859082 := by exact prefixLift 2859082
  have htrace : WordTrace (prefixWord ++ tailWord_2859082) baseStart_2859082 baseEnd_2859082 := by
    simpa [prefixWord, tailWord_2859082, baseEnd_2859082] using wordTrace_append hprefix tailTrace_2859082
  have hstable : (prefixWord ++ tailWord_2859082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859082).length < 2 ^ (prefixWord ++ tailWord_2859082).sum := by decide
  have hdescent : baseEnd_2859082 < baseStart_2859082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859086 : List Nat := [4, 1, 1, 1, 1, 6, 1, 1, 3, 4]
def baseStart_2859086 : Nat := 118140960795 + 2859086 * 2 ^ 59
def prefixEnd_2859086 : Nat := 4983230072969 + 3 ^ 40 * 2859086 * 2
def baseEnd_2859086 : Nat := 489361783513568682192103

theorem tailTrace_2859086 : CollatzResearch.WordTrace tailWord_2859086 prefixEnd_2859086 489361783513568682192103 := by
  unfold tailWord_2859086
  simp only [CollatzResearch.WordTrace]
  refine ⟨13034929165003398732364639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69519622213351459905944741 13034929165003398732364639)
  ·
    refine ⟨19552393747505098098546959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13034929165003398732364639 19552393747505098098546959)
    ·
      refine ⟨29328590621257647147820439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19552393747505098098546959 29328590621257647147820439)
      ·
        refine ⟨43992885931886470721730659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29328590621257647147820439 43992885931886470721730659)
        ·
          refine ⟨65989328897829706082595989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43992885931886470721730659 65989328897829706082595989)
          ·
            refine ⟨3093249792085767472621687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 65989328897829706082595989 3093249792085767472621687)
            ·
              refine ⟨4639874688128651208932531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3093249792085767472621687 4639874688128651208932531)
              ·
                refine ⟨6959812032192976813398797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4639874688128651208932531 6959812032192976813398797)
                ·
                  refine ⟨2609929512072366305024549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6959812032192976813398797 2609929512072366305024549)
                  ·
                    refine ⟨489361783513568682192103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2609929512072366305024549 489361783513568682192103)
                    ·
                      rfl

theorem cell23_2859086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 1, 3, 4].length) (baseStart_2859086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2859086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2859086 prefixEnd_2859086 := by exact prefixLift 2859086
  have htrace : WordTrace (prefixWord ++ tailWord_2859086) baseStart_2859086 baseEnd_2859086 := by
    simpa [prefixWord, tailWord_2859086, baseEnd_2859086] using wordTrace_append hprefix tailTrace_2859086
  have hstable : (prefixWord ++ tailWord_2859086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859086).length < 2 ^ (prefixWord ++ tailWord_2859086).sum := by decide
  have hdescent : baseEnd_2859086 < baseStart_2859086 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859137 : List Nat := [1, 2, 4, 2, 4, 1, 2, 2, 1, 4]
def baseStart_2859137 : Nat := 118140960795 + 2859137 * 2 ^ 59
def prefixEnd_2859137 : Nat := 4983230072969 + 3 ^ 40 * 2859137 * 2
def baseEnd_2859137 : Nat := 489370512684695115679525

theorem tailTrace_2859137 : CollatzResearch.WordTrace tailWord_2859137 prefixEnd_2859137 489370512684695115679525 := by
  unfold tailWord_2859137
  simp only [CollatzResearch.WordTrace]
  refine ⟨104281293442842425569023665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69520862295228283712682443 104281293442842425569023665)
  ·
    refine ⟨78210970082131819176767749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104281293442842425569023665 78210970082131819176767749)
    ·
      refine ⟨14664556890399716095643953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78210970082131819176767749 14664556890399716095643953)
      ·
        refine ⟨10998417667799787071732965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14664556890399716095643953 10998417667799787071732965)
        ·
          refine ⟨2062203312712460075949931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10998417667799787071732965 2062203312712460075949931)
          ·
            refine ⟨3093304969068690113924897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2062203312712460075949931 3093304969068690113924897)
            ·
              refine ⟨2319978726801517585443673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3093304969068690113924897 2319978726801517585443673)
              ·
                refine ⟨1739984045101138189082755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2319978726801517585443673 1739984045101138189082755)
                ·
                  refine ⟨2609976067651707283624133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1739984045101138189082755 2609976067651707283624133)
                  ·
                    refine ⟨489370512684695115679525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2609976067651707283624133 489370512684695115679525)
                    ·
                      rfl

theorem cell23_2859137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 2, 2, 1, 4].length) (baseStart_2859137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2859137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2859137 prefixEnd_2859137 := by exact prefixLift 2859137
  have htrace : WordTrace (prefixWord ++ tailWord_2859137) baseStart_2859137 baseEnd_2859137 := by
    simpa [prefixWord, tailWord_2859137, baseEnd_2859137] using wordTrace_append hprefix tailTrace_2859137
  have hstable : (prefixWord ++ tailWord_2859137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859137).length < 2 ^ (prefixWord ++ tailWord_2859137).sum := by decide
  have hdescent : baseEnd_2859137 < baseStart_2859137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859152 : List Nat := [2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 5]
def baseStart_2859152 : Nat := 118140960795 + 2859152 * 2 ^ 59
def prefixEnd_2859152 : Nat := 4983230072969 + 3 ^ 40 * 2859152 * 2
def baseEnd_2859152 : Nat := 1468119240263902788351005

theorem tailTrace_2859152 : CollatzResearch.WordTrace tailWord_2859152 prefixEnd_2859152 1468119240263902788351005 := by
  unfold tailWord_2859152
  simp only [CollatzResearch.WordTrace]
  refine ⟨52140920268894041565409855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69521227025192055420546473 52140920268894041565409855)
  ·
    refine ⟨78211380403341062348114783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52140920268894041565409855 78211380403341062348114783)
    ·
      refine ⟨117317070605011593522172175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78211380403341062348114783 117317070605011593522172175)
      ·
        refine ⟨175975605907517390283258263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117317070605011593522172175 175975605907517390283258263)
        ·
          refine ⟨263963408861276085424887395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175975605907517390283258263 263963408861276085424887395)
          ·
            refine ⟨395945113291914128137331093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263963408861276085424887395 395945113291914128137331093)
            ·
              refine ⟨18559927185558474756437395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 395945113291914128137331093 18559927185558474756437395)
              ·
                refine ⟨27839890778337712134656093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18559927185558474756437395 27839890778337712134656093)
                ·
                  refine ⟨10439959041876642050496035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27839890778337712134656093 10439959041876642050496035)
                  ·
                    refine ⟨15659938562814963075744053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10439959041876642050496035 15659938562814963075744053)
                    ·
                      refine ⟨1468119240263902788351005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15659938562814963075744053 1468119240263902788351005)
                      ·
                        rfl

theorem cell23_2859152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 5].length) (baseStart_2859152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2859152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2859152 prefixEnd_2859152 := by exact prefixLift 2859152
  have htrace : WordTrace (prefixWord ++ tailWord_2859152) baseStart_2859152 baseEnd_2859152 := by
    simpa [prefixWord, tailWord_2859152, baseEnd_2859152] using wordTrace_append hprefix tailTrace_2859152
  have hstable : (prefixWord ++ tailWord_2859152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859152).length < 2 ^ (prefixWord ++ tailWord_2859152).sum := by decide
  have hdescent : baseEnd_2859152 < baseStart_2859152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859170 : List Nat := [3, 3, 1, 3, 1, 3, 1, 1, 2, 3, 2]
def baseStart_2859170 : Nat := 118140960795 + 2859170 * 2 ^ 59
def prefixEnd_2859170 : Nat := 4983230072969 + 3 ^ 40 * 2859170 * 2
def baseEnd_2859170 : Nat := 1468128482915683717925923

theorem tailTrace_2859170 : CollatzResearch.WordTrace tailWord_2859170 prefixEnd_2859170 1468128482915683717925923 := by
  unfold tailWord_2859170
  simp only [CollatzResearch.WordTrace]
  refine ⟨26070624262930718051243741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69521664701148581469983309 26070624262930718051243741)
  ·
    refine ⟨9776484098599019269216403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26070624262930718051243741 9776484098599019269216403)
    ·
      refine ⟨14664726147898528903824605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9776484098599019269216403 14664726147898528903824605)
      ·
        refine ⟨5499272305461948338934227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14664726147898528903824605 5499272305461948338934227)
        ·
          refine ⟨8248908458192922508401341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5499272305461948338934227 8248908458192922508401341)
          ·
            refine ⟨3093340671822345940650503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8248908458192922508401341 3093340671822345940650503)
            ·
              refine ⟨4640011007733518910975755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3093340671822345940650503 4640011007733518910975755)
              ·
                refine ⟨6960016511600278366463633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4640011007733518910975755 6960016511600278366463633)
                ·
                  refine ⟨5220012383700208774847725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6960016511600278366463633 5220012383700208774847725)
                  ·
                    refine ⟨1957504643887578290567897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5220012383700208774847725 1957504643887578290567897)
                    ·
                      refine ⟨1468128482915683717925923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1957504643887578290567897 1468128482915683717925923)
                      ·
                        rfl

theorem cell23_2859170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_2859170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2859170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2859170 prefixEnd_2859170 := by exact prefixLift 2859170
  have htrace : WordTrace (prefixWord ++ tailWord_2859170) baseStart_2859170 baseEnd_2859170 := by
    simpa [prefixWord, tailWord_2859170, baseEnd_2859170] using wordTrace_append hprefix tailTrace_2859170
  have hstable : (prefixWord ++ tailWord_2859170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859170).length < 2 ^ (prefixWord ++ tailWord_2859170).sum := by decide
  have hdescent : baseEnd_2859170 < baseStart_2859170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859186 : List Nat := [3, 2, 1, 1, 1, 3, 3, 3, 1, 2, 3]
def baseStart_2859186 : Nat := 118140960795 + 2859186 * 2 ^ 59
def prefixEnd_2859186 : Nat := 4983230072969 + 3 ^ 40 * 2859186 * 2
def baseEnd_2859186 : Nat := 1468136698606155655325849

theorem tailTrace_2859186 : CollatzResearch.WordTrace tailWord_2859186 prefixEnd_2859186 1468136698606155655325849 := by
  unfold tailWord_2859186
  simp only [CollatzResearch.WordTrace]
  refine ⟨26070770154916226734389353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69522053746443271291704941 26070770154916226734389353)
  ·
    refine ⟨19553077616187170050792015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26070770154916226734389353 19553077616187170050792015)
    ·
      refine ⟨29329616424280755076188023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19553077616187170050792015 29329616424280755076188023)
      ·
        refine ⟨43994424636421132614282035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29329616424280755076188023 43994424636421132614282035)
        ·
          refine ⟨65991636954631698921423053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43994424636421132614282035 65991636954631698921423053)
          ·
            refine ⟨24746863857986887095533645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65991636954631698921423053 24746863857986887095533645)
            ·
              refine ⟨9280073946745082660825117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24746863857986887095533645 9280073946745082660825117)
              ·
                refine ⟨3480027730029405997809419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9280073946745082660825117 3480027730029405997809419)
                ·
                  refine ⟨5220041595044108996714129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3480027730029405997809419 5220041595044108996714129)
                  ·
                    refine ⟨3915031196283081747535597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5220041595044108996714129 3915031196283081747535597)
                    ·
                      refine ⟨1468136698606155655325849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3915031196283081747535597 1468136698606155655325849)
                      ·
                        rfl

theorem cell23_2859186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 3, 1, 2, 3].length) (baseStart_2859186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2859186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2859186 prefixEnd_2859186 := by exact prefixLift 2859186
  have htrace : WordTrace (prefixWord ++ tailWord_2859186) baseStart_2859186 baseEnd_2859186 := by
    simpa [prefixWord, tailWord_2859186, baseEnd_2859186] using wordTrace_append hprefix tailTrace_2859186
  have hstable : (prefixWord ++ tailWord_2859186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859186).length < 2 ^ (prefixWord ++ tailWord_2859186).sum := by decide
  have hdescent : baseEnd_2859186 < baseStart_2859186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859200 : List Nat := [2, 1, 1, 2, 5, 1, 2, 4, 1, 2, 2]
def baseStart_2859200 : Nat := 118140960795 + 2859200 * 2 ^ 59
def prefixEnd_2859200 : Nat := 4983230072969 + 3 ^ 40 * 2859200 * 2
def baseEnd_2859200 : Nat := 1468143887335318600550785

theorem tailTrace_2859200 : CollatzResearch.WordTrace tailWord_2859200 prefixEnd_2859200 1468143887335318600550785 := by
  unfold tailWord_2859200
  simp only [CollatzResearch.WordTrace]
  refine ⟨52141795620807093664283527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69522394161076124885711369 52141795620807093664283527)
  ·
    refine ⟨78212693431210640496425291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52141795620807093664283527 78212693431210640496425291)
    ·
      refine ⟨117319040146815960744637937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78212693431210640496425291 117319040146815960744637937)
      ·
        refine ⟨87989280110111970558478453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117319040146815960744637937 87989280110111970558478453)
        ·
          refine ⟨8248995010322997239857355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 87989280110111970558478453 8248995010322997239857355)
          ·
            refine ⟨12373492515484495859786033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8248995010322997239857355 12373492515484495859786033)
            ·
              refine ⟨9280119386613371894839525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12373492515484495859786033 9280119386613371894839525)
              ·
                refine ⟨1740022384990007230282411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9280119386613371894839525 1740022384990007230282411)
                ·
                  refine ⟨2610033577485010845423617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1740022384990007230282411 2610033577485010845423617)
                  ·
                    refine ⟨1957525183113758134067713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2610033577485010845423617 1957525183113758134067713)
                    ·
                      refine ⟨1468143887335318600550785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1957525183113758134067713 1468143887335318600550785)
                      ·
                        rfl

theorem cell23_2859200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 4, 1, 2, 2].length) (baseStart_2859200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2859200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2859200 prefixEnd_2859200 := by exact prefixLift 2859200
  have htrace : WordTrace (prefixWord ++ tailWord_2859200) baseStart_2859200 baseEnd_2859200 := by
    simpa [prefixWord, tailWord_2859200, baseEnd_2859200] using wordTrace_append hprefix tailTrace_2859200
  have hstable : (prefixWord ++ tailWord_2859200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859200).length < 2 ^ (prefixWord ++ tailWord_2859200).sum := by decide
  have hdescent : baseEnd_2859200 < baseStart_2859200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859209 : List Nat := [1, 2, 1, 1, 2, 1, 1, 3, 2, 7, 2]
def baseStart_2859209 : Nat := 118140960795 + 2859209 * 2 ^ 59
def prefixEnd_2859209 : Nat := 4983230072969 + 3 ^ 40 * 2859209 * 2
def baseEnd_2859209 : Nat := 1468148508661209065338243

theorem tailTrace_2859209 : CollatzResearch.WordTrace tailWord_2859209 prefixEnd_2859209 1468148508661209065338243 := by
  unfold tailWord_2859209
  simp only [CollatzResearch.WordTrace]
  refine ⟨104283919498581581865644681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69522612999054387910429787 104283919498581581865644681)
  ·
    refine ⟨78212939623936186399233511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104283919498581581865644681 78212939623936186399233511)
    ·
      refine ⟨117319409435904279598850267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78212939623936186399233511 117319409435904279598850267)
      ·
        refine ⟨175979114153856419398275401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117319409435904279598850267 175979114153856419398275401)
        ·
          refine ⟨131984335615392314548706551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175979114153856419398275401 131984335615392314548706551)
          ·
            refine ⟨197976503423088471823059827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131984335615392314548706551 197976503423088471823059827)
            ·
              refine ⟨296964755134632707734589741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197976503423088471823059827 296964755134632707734589741)
              ·
                refine ⟨111361783175487265400471153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 296964755134632707734589741 111361783175487265400471153)
                ·
                  refine ⟨83521337381615449050353365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111361783175487265400471153 83521337381615449050353365)
                  ·
                    refine ⟨1957531344881612087117657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 83521337381615449050353365 1957531344881612087117657)
                    ·
                      refine ⟨1468148508661209065338243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1957531344881612087117657 1468148508661209065338243)
                      ·
                        rfl

theorem cell23_2859209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 7, 2].length) (baseStart_2859209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2859209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2859209 prefixEnd_2859209 := by exact prefixLift 2859209
  have htrace : WordTrace (prefixWord ++ tailWord_2859209) baseStart_2859209 baseEnd_2859209 := by
    simpa [prefixWord, tailWord_2859209, baseEnd_2859209] using wordTrace_append hprefix tailTrace_2859209
  have hstable : (prefixWord ++ tailWord_2859209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859209).length < 2 ^ (prefixWord ++ tailWord_2859209).sum := by decide
  have hdescent : baseEnd_2859209 < baseStart_2859209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859226 : List Nat := [3, 1, 1, 2, 2, 1, 2, 3, 3, 3, 2]
def baseStart_2859226 : Nat := 118140960795 + 2859226 * 2 ^ 59
def prefixEnd_2859226 : Nat := 4983230072969 + 3 ^ 40 * 2859226 * 2
def baseEnd_2859226 : Nat := 1468157237832335498825665

theorem tailTrace_2859226 : CollatzResearch.WordTrace tailWord_2859226 prefixEnd_2859226 1468157237832335498825665 := by
  unfold tailWord_2859226
  simp only [CollatzResearch.WordTrace]
  refine ⟨26071134884879998442253383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69523026359679995846009021 26071134884879998442253383)
  ·
    refine ⟨39106702327319997663380075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26071134884879998442253383 39106702327319997663380075)
    ·
      refine ⟨58660053490979996495070113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39106702327319997663380075 58660053490979996495070113)
      ·
        refine ⟨43995040118234997371302585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58660053490979996495070113 43995040118234997371302585)
        ·
          refine ⟨32996280088676248028476939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43995040118234997371302585 32996280088676248028476939)
          ·
            refine ⟨49494420133014372042715409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32996280088676248028476939 49494420133014372042715409)
            ·
              refine ⟨37120815099760779032036557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49494420133014372042715409 37120815099760779032036557)
              ·
                refine ⟨13920305662410292137013709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37120815099760779032036557 13920305662410292137013709)
                ·
                  refine ⟨5220114623403859551380141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13920305662410292137013709 5220114623403859551380141)
                  ·
                    refine ⟨1957542983776447331767553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5220114623403859551380141 1957542983776447331767553)
                    ·
                      refine ⟨1468157237832335498825665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1957542983776447331767553 1468157237832335498825665)
                      ·
                        rfl

theorem cell23_2859226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 3, 3, 2].length) (baseStart_2859226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2859226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2859226 prefixEnd_2859226 := by exact prefixLift 2859226
  have htrace : WordTrace (prefixWord ++ tailWord_2859226) baseStart_2859226 baseEnd_2859226 := by
    simpa [prefixWord, tailWord_2859226, baseEnd_2859226] using wordTrace_append hprefix tailTrace_2859226
  have hstable : (prefixWord ++ tailWord_2859226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859226).length < 2 ^ (prefixWord ++ tailWord_2859226).sum := by decide
  have hdescent : baseEnd_2859226 < baseStart_2859226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859294 : List Nat := [4, 3, 2, 1, 1, 2, 3, 1, 1, 3, 2]
def baseStart_2859294 : Nat := 118140960795 + 2859294 * 2 ^ 59
def prefixEnd_2859294 : Nat := 4983230072969 + 3 ^ 40 * 2859294 * 2
def baseEnd_2859294 : Nat := 1468192154516841232775353

theorem tailTrace_2859294 : CollatzResearch.WordTrace tailWord_2859294 prefixEnd_2859294 1468192154516841232775353 := by
  unfold tailWord_2859294
  simp only [CollatzResearch.WordTrace]
  refine ⟨13035877462909205172811117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69524679802182427588325957 13035877462909205172811117)
  ·
    refine ⟨4888454048590951939804169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13035877462909205172811117 4888454048590951939804169)
    ·
      refine ⟨3666340536443213954853127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4888454048590951939804169 3666340536443213954853127)
      ·
        refine ⟨5499510804664820932279691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3666340536443213954853127 5499510804664820932279691)
        ·
          refine ⟨8249266206997231398419537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5499510804664820932279691 8249266206997231398419537)
          ·
            refine ⟨6186949655247923548814653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8249266206997231398419537 6186949655247923548814653)
            ·
              refine ⟨2320106120717971330805495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6186949655247923548814653 2320106120717971330805495)
              ·
                refine ⟨3480159181076956996208243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2320106120717971330805495 3480159181076956996208243)
                ·
                  refine ⟨5220238771615435494312365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3480159181076956996208243 5220238771615435494312365)
                  ·
                    refine ⟨1957589539355788310367137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5220238771615435494312365 1957589539355788310367137)
                    ·
                      refine ⟨1468192154516841232775353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1957589539355788310367137 1468192154516841232775353)
                      ·
                        rfl

theorem cell23_2859294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_2859294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2859294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2859294 prefixEnd_2859294 := by exact prefixLift 2859294
  have htrace : WordTrace (prefixWord ++ tailWord_2859294) baseStart_2859294 baseEnd_2859294 := by
    simpa [prefixWord, tailWord_2859294, baseEnd_2859294] using wordTrace_append hprefix tailTrace_2859294
  have hstable : (prefixWord ++ tailWord_2859294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859294).length < 2 ^ (prefixWord ++ tailWord_2859294).sum := by decide
  have hdescent : baseEnd_2859294 < baseStart_2859294 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859313 : List Nat := [1, 2, 2, 3, 4, 1, 1, 4, 5]
def baseStart_2859313 : Nat := 118140960795 + 2859313 * 2 ^ 59
def prefixEnd_2859313 : Nat := 4983230072969 + 3 ^ 40 * 2859313 * 2
def baseEnd_2859313 : Nat := 163133545627697406493085

theorem tailTrace_2859313 : CollatzResearch.WordTrace tailWord_2859313 prefixEnd_2859313 163133545627697406493085 := by
  unfold tailWord_2859313
  simp only [CollatzResearch.WordTrace]
  refine ⟨104287712690204807627430593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69525141793469871751620395 104287712690204807627430593)
  ·
    refine ⟨78215784517653605720572945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104287712690204807627430593 78215784517653605720572945)
    ·
      refine ⟨58661838388240204290429709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78215784517653605720572945 58661838388240204290429709)
      ·
        refine ⟨21998189395590076608911141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58661838388240204290429709 21998189395590076608911141)
        ·
          refine ⟨4124660511673139364170839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21998189395590076608911141 4124660511673139364170839)
          ·
            refine ⟨6186990767509709046256259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4124660511673139364170839 6186990767509709046256259)
            ·
              refine ⟨9280486151264563569384389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6186990767509709046256259 9280486151264563569384389)
              ·
                refine ⟨1740091153362105669259573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9280486151264563569384389 1740091153362105669259573)
                ·
                  refine ⟨163133545627697406493085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1740091153362105669259573 163133545627697406493085)
                  ·
                    rfl

theorem cell23_2859313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 4, 5].length) (baseStart_2859313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2859313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2859313 prefixEnd_2859313 := by exact prefixLift 2859313
  have htrace : WordTrace (prefixWord ++ tailWord_2859313) baseStart_2859313 baseEnd_2859313 := by
    simpa [prefixWord, tailWord_2859313, baseEnd_2859313] using wordTrace_append hprefix tailTrace_2859313
  have hstable : (prefixWord ++ tailWord_2859313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859313).length < 2 ^ (prefixWord ++ tailWord_2859313).sum := by decide
  have hdescent : baseEnd_2859313 < baseStart_2859313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859359 : List Nat := [1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 6]
def baseStart_2859359 : Nat := 118140960795 + 2859359 * 2 ^ 59
def prefixEnd_2859359 : Nat := 4983230072969 + 3 ^ 40 * 2859359 * 2
def baseEnd_2859359 : Nat := 1468225530759383478462553

theorem tailTrace_2859359 : CollatzResearch.WordTrace tailWord_2859359 prefixEnd_2859359 1468225530759383478462553 := by
  unfold tailWord_2859359
  simp only [CollatzResearch.WordTrace]
  refine ⟨104289390448038157483605131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69526260298692104989070087 104289390448038157483605131)
  ·
    refine ⟨156434085672057236225407697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104289390448038157483605131 156434085672057236225407697)
    ·
      refine ⟨117325564254042927169055773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156434085672057236225407697 117325564254042927169055773)
      ·
        refine ⟨43997086595266097688395915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117325564254042927169055773 43997086595266097688395915)
        ·
          refine ⟨65995629892899146532593873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43997086595266097688395915 65995629892899146532593873)
          ·
            refine ⟨49496722419674359899445405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65995629892899146532593873 49496722419674359899445405)
            ·
              refine ⟨18561270907377884962292027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49496722419674359899445405 18561270907377884962292027)
              ·
                refine ⟨27841906361066827443438041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18561270907377884962292027 27841906361066827443438041)
                ·
                  refine ⟨20881429770800120582578531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27841906361066827443438041 20881429770800120582578531)
                  ·
                    refine ⟨31322144656200180873867797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20881429770800120582578531 31322144656200180873867797)
                    ·
                      refine ⟨1468225530759383478462553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31322144656200180873867797 1468225530759383478462553)
                      ·
                        rfl

theorem cell23_2859359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 6].length) (baseStart_2859359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2859359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2859359 prefixEnd_2859359 := by exact prefixLift 2859359
  have htrace : WordTrace (prefixWord ++ tailWord_2859359) baseStart_2859359 baseEnd_2859359 := by
    simpa [prefixWord, tailWord_2859359, baseEnd_2859359] using wordTrace_append hprefix tailTrace_2859359
  have hstable : (prefixWord ++ tailWord_2859359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859359).length < 2 ^ (prefixWord ++ tailWord_2859359).sum := by decide
  have hdescent : baseEnd_2859359 < baseStart_2859359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859369 : List Nat := [1, 2, 1, 1, 1, 3, 5, 1, 8]
def baseStart_2859369 : Nat := 118140960795 + 2859369 * 2 ^ 59
def prefixEnd_2859369 : Nat := 4983230072969 + 3 ^ 40 * 2859369 * 2
def baseEnd_2859369 : Nat := 163136740618436493259723

theorem tailTrace_2859369 : CollatzResearch.WordTrace tailWord_2859369 prefixEnd_2859369 163136740618436493259723 := by
  unfold tailWord_2859369
  simp only [CollatzResearch.WordTrace]
  refine ⟨104289755178001929191469161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69526503452001286127646107 104289755178001929191469161)
  ·
    refine ⟨78217316383501446893601871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104289755178001929191469161 78217316383501446893601871)
    ·
      refine ⟨117325974575252170340402807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78217316383501446893601871 117325974575252170340402807)
      ·
        refine ⟨175988961862878255510604211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117325974575252170340402807 175988961862878255510604211)
        ·
          refine ⟨263983442794317383265906317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175988961862878255510604211 263983442794317383265906317)
          ·
            refine ⟨98993791047869018724714869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 263983442794317383265906317 98993791047869018724714869)
            ·
              refine ⟨9280667910737720505442019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 98993791047869018724714869 9280667910737720505442019)
              ·
                refine ⟨13921001866106580758163029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9280667910737720505442019 13921001866106580758163029)
                ·
                  refine ⟨163136740618436493259723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13921001866106580758163029 163136740618436493259723)
                  ·
                    rfl

theorem cell23_2859369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 8].length) (baseStart_2859369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2859369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2859369 prefixEnd_2859369 := by exact prefixLift 2859369
  have htrace : WordTrace (prefixWord ++ tailWord_2859369) baseStart_2859369 baseEnd_2859369 := by
    simpa [prefixWord, tailWord_2859369, baseEnd_2859369] using wordTrace_append hprefix tailTrace_2859369
  have hstable : (prefixWord ++ tailWord_2859369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859369).length < 2 ^ (prefixWord ++ tailWord_2859369).sum := by decide
  have hdescent : baseEnd_2859369 < baseStart_2859369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859373 : List Nat := [1, 5, 1, 1, 1, 2, 4, 1, 3, 4]
def baseStart_2859373 : Nat := 118140960795 + 2859373 * 2 ^ 59
def prefixEnd_2859373 : Nat := 4983230072969 + 3 ^ 40 * 2859373 * 2
def baseEnd_2859373 : Nat := 489410906496182141229163

theorem tailTrace_2859373 : CollatzResearch.WordTrace tailWord_2859373 prefixEnd_2859373 489410906496182141229163 := by
  unfold tailWord_2859373
  simp only [CollatzResearch.WordTrace]
  refine ⟨104289901069987437874614773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69526600713324958583076515 104289901069987437874614773)
  ·
    refine ⟨9777178225311322300745135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 104289901069987437874614773 9777178225311322300745135)
    ·
      refine ⟨14665767337966983451117703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9777178225311322300745135 14665767337966983451117703)
      ·
        refine ⟨21998651006950475176676555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14665767337966983451117703 21998651006950475176676555)
        ·
          refine ⟨32997976510425712765014833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21998651006950475176676555 32997976510425712765014833)
          ·
            refine ⟨24748482382819284573761125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32997976510425712765014833 24748482382819284573761125)
            ·
              refine ⟨4640340446778615857580211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24748482382819284573761125 4640340446778615857580211)
              ·
                refine ⟨6960510670167923786370317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4640340446778615857580211 6960510670167923786370317)
                ·
                  refine ⟨2610191501312971419888869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6960510670167923786370317 2610191501312971419888869)
                  ·
                    refine ⟨489410906496182141229163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2610191501312971419888869 489410906496182141229163)
                    ·
                      rfl

theorem cell23_2859373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 1, 3, 4].length) (baseStart_2859373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2859373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2859373 prefixEnd_2859373 := by exact prefixLift 2859373
  have htrace : WordTrace (prefixWord ++ tailWord_2859373) baseStart_2859373 baseEnd_2859373 := by
    simpa [prefixWord, tailWord_2859373, baseEnd_2859373] using wordTrace_append hprefix tailTrace_2859373
  have hstable : (prefixWord ++ tailWord_2859373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859373).length < 2 ^ (prefixWord ++ tailWord_2859373).sum := by decide
  have hdescent : baseEnd_2859373 < baseStart_2859373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859396 : List Nat := [2, 3, 2, 1, 1, 2, 1, 1, 2, 5, 3]
def baseStart_2859396 : Nat := 118140960795 + 2859396 * 2 ^ 59
def prefixEnd_2859396 : Nat := 4983230072969 + 3 ^ 40 * 2859396 * 2
def baseEnd_2859396 : Nat := 1468244529543599833699883

theorem tailTrace_2859396 : CollatzResearch.WordTrace tailWord_2859396 prefixEnd_2859396 1468244529543599833699883 := by
  unfold tailWord_2859396
  simp only [CollatzResearch.WordTrace]
  refine ⟨52145369974452056401351021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69527159965936075201801361 52145369974452056401351021)
  ·
    refine ⟨19554513740419521150506633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52145369974452056401351021 19554513740419521150506633)
    ·
      refine ⟨14665885305314640862879975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19554513740419521150506633 14665885305314640862879975)
      ·
        refine ⟨21998827957971961294319963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14665885305314640862879975 21998827957971961294319963)
        ·
          refine ⟨32998241936957941941479945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21998827957971961294319963 32998241936957941941479945)
          ·
            refine ⟨24748681452718456456109959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32998241936957941941479945 24748681452718456456109959)
            ·
              refine ⟨37123022179077684684164939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24748681452718456456109959 37123022179077684684164939)
              ·
                refine ⟨55684533268616527026247409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37123022179077684684164939 55684533268616527026247409)
                ·
                  refine ⟨41763399951462395269685557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55684533268616527026247409 41763399951462395269685557)
                  ·
                    refine ⟨3915318745449599556533021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41763399951462395269685557 3915318745449599556533021)
                    ·
                      refine ⟨1468244529543599833699883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3915318745449599556533021 1468244529543599833699883)
                      ·
                        rfl

theorem cell23_2859396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 2, 5, 3].length) (baseStart_2859396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2859396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2859396 prefixEnd_2859396 := by exact prefixLift 2859396
  have htrace : WordTrace (prefixWord ++ tailWord_2859396) baseStart_2859396 baseEnd_2859396 := by
    simpa [prefixWord, tailWord_2859396, baseEnd_2859396] using wordTrace_append hprefix tailTrace_2859396
  have hstable : (prefixWord ++ tailWord_2859396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859396).length < 2 ^ (prefixWord ++ tailWord_2859396).sum := by decide
  have hdescent : baseEnd_2859396 < baseStart_2859396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859409 : List Nat := [1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 5]
def baseStart_2859409 : Nat := 118140960795 + 2859409 * 2 ^ 59
def prefixEnd_2859409 : Nat := 4983230072969 + 3 ^ 40 * 2859409 * 2
def baseEnd_2859409 : Nat := 1468251204792108282837323

theorem tailTrace_2859409 : CollatzResearch.WordTrace tailWord_2859409 prefixEnd_2859409 1468251204792108282837323 := by
  unfold tailWord_2859409
  simp only [CollatzResearch.WordTrace]
  refine ⟨104291214097857016022925281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69527476065238010681950187 104291214097857016022925281)
  ·
    refine ⟨78218410573392762017193961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104291214097857016022925281 78218410573392762017193961)
    ·
      refine ⟨58663807930044571512895471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78218410573392762017193961 58663807930044571512895471)
      ·
        refine ⟨87995711895066857269343207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58663807930044571512895471 87995711895066857269343207)
        ·
          refine ⟨131993567842600285904014811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87995711895066857269343207 131993567842600285904014811)
          ·
            refine ⟨197990351763900428856022217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131993567842600285904014811 197990351763900428856022217)
            ·
              refine ⟨148492763822925321642016663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 197990351763900428856022217 148492763822925321642016663)
              ·
                refine ⟨222739145734387982463024995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148492763822925321642016663 222739145734387982463024995)
                ·
                  refine ⟨334108718601581973694537493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 222739145734387982463024995 334108718601581973694537493)
                  ·
                    refine ⟨15661346184449155016931445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 334108718601581973694537493 15661346184449155016931445)
                    ·
                      refine ⟨1468251204792108282837323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15661346184449155016931445 1468251204792108282837323)
                      ·
                        rfl

theorem cell23_2859409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 5].length) (baseStart_2859409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2859409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2859409 prefixEnd_2859409 := by exact prefixLift 2859409
  have htrace : WordTrace (prefixWord ++ tailWord_2859409) baseStart_2859409 baseEnd_2859409 := by
    simpa [prefixWord, tailWord_2859409, baseEnd_2859409] using wordTrace_append hprefix tailTrace_2859409
  have hstable : (prefixWord ++ tailWord_2859409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859409).length < 2 ^ (prefixWord ++ tailWord_2859409).sum := by decide
  have hdescent : baseEnd_2859409 < baseStart_2859409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859414 : List Nat := [5, 3, 1, 2, 1, 1, 1, 2, 2, 1, 4]
def baseStart_2859414 : Nat := 118140960795 + 2859414 * 2 ^ 59
def prefixEnd_2859414 : Nat := 4983230072969 + 3 ^ 40 * 2859414 * 2
def baseEnd_2859414 : Nat := 1468253772195380763274801

theorem tailTrace_2859414 : CollatzResearch.WordTrace tailWord_2859414 prefixEnd_2859414 1468253772195380763274801 := by
  unfold tailWord_2859414
  simp only [CollatzResearch.WordTrace]
  refine ⟨6518212278927431367303581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69527597641892601251238197 6518212278927431367303581)
  ·
    refine ⟨2444329604597786762738843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6518212278927431367303581 2444329604597786762738843)
    ·
      refine ⟨3666494406896680144108265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2444329604597786762738843 3666494406896680144108265)
      ·
        refine ⟨2749870805172510108081199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3666494406896680144108265 2749870805172510108081199)
        ·
          refine ⟨4124806207758765162121799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2749870805172510108081199 4124806207758765162121799)
          ·
            refine ⟨6187209311638147743182699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4124806207758765162121799 6187209311638147743182699)
            ·
              refine ⟨9280813967457221614774049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6187209311638147743182699 9280813967457221614774049)
              ·
                refine ⟨6960610475592916211080537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9280813967457221614774049 6960610475592916211080537)
                ·
                  refine ⟨5220457856694687158310403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6960610475592916211080537 5220457856694687158310403)
                  ·
                    refine ⟨7830686785042030737465605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5220457856694687158310403 7830686785042030737465605)
                    ·
                      refine ⟨1468253772195380763274801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7830686785042030737465605 1468253772195380763274801)
                      ·
                        rfl

theorem cell23_2859414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_2859414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2859414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2859414 prefixEnd_2859414 := by exact prefixLift 2859414
  have htrace : WordTrace (prefixWord ++ tailWord_2859414) baseStart_2859414 baseEnd_2859414 := by
    simpa [prefixWord, tailWord_2859414, baseEnd_2859414] using wordTrace_append hprefix tailTrace_2859414
  have hstable : (prefixWord ++ tailWord_2859414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859414).length < 2 ^ (prefixWord ++ tailWord_2859414).sum := by decide
  have hdescent : baseEnd_2859414 < baseStart_2859414 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859436 : List Nat := [2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 4]
def baseStart_2859436 : Nat := 118140960795 + 2859436 * 2 ^ 59
def prefixEnd_2859436 : Nat := 4983230072969 + 3 ^ 40 * 2859436 * 2
def baseEnd_2859436 : Nat := 1468265068769779677199699

theorem tailTrace_2859436 : CollatzResearch.WordTrace tailWord_2859436 prefixEnd_2859436 1468265068769779677199699 := by
  unfold tailWord_2859436
  simp only [CollatzResearch.WordTrace]
  refine ⟨52146099434379599817079081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69528132579172799756105441 52146099434379599817079081)
  ·
    refine ⟨39109574575784699862809311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52146099434379599817079081 39109574575784699862809311)
    ·
      refine ⟨58664361863677049794213967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39109574575784699862809311 58664361863677049794213967)
      ·
        refine ⟨87996542795515574691320951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58664361863677049794213967 87996542795515574691320951)
        ·
          refine ⟨131994814193273362036981427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87996542795515574691320951 131994814193273362036981427)
          ·
            refine ⟨197992221289910043055472141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131994814193273362036981427 197992221289910043055472141)
            ·
              refine ⟨74247082983716266145802053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 197992221289910043055472141 74247082983716266145802053)
              ·
                refine ⟨13921328059446799902337885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74247082983716266145802053 13921328059446799902337885)
                ·
                  refine ⟨5220498022292549963376707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13921328059446799902337885 5220498022292549963376707)
                  ·
                    refine ⟨7830747033438824945065061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5220498022292549963376707 7830747033438824945065061)
                    ·
                      refine ⟨1468265068769779677199699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7830747033438824945065061 1468265068769779677199699)
                      ·
                        rfl

theorem cell23_2859436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 4].length) (baseStart_2859436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2859436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2859436 prefixEnd_2859436 := by exact prefixLift 2859436
  have htrace : WordTrace (prefixWord ++ tailWord_2859436) baseStart_2859436 baseEnd_2859436 := by
    simpa [prefixWord, tailWord_2859436, baseEnd_2859436] using wordTrace_append hprefix tailTrace_2859436
  have hstable : (prefixWord ++ tailWord_2859436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859436).length < 2 ^ (prefixWord ++ tailWord_2859436).sum := by decide
  have hdescent : baseEnd_2859436 < baseStart_2859436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859437 : List Nat := [1, 5, 2, 2, 2, 2, 2, 1, 6]
def baseStart_2859437 : Nat := 118140960795 + 2859437 * 2 ^ 59
def prefixEnd_2859437 : Nat := 4983230072969 + 3 ^ 40 * 2859437 * 2
def baseEnd_2859437 : Nat := 163140620250048241476355

theorem tailTrace_2859437 : CollatzResearch.WordTrace tailWord_2859437 prefixEnd_2859437 163140620250048241476355 := by
  unfold tailWord_2859437
  simp only [CollatzResearch.WordTrace]
  refine ⟨104292235341755576804944565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69528156894503717869963043 104292235341755576804944565)
  ·
    refine ⟨9777397063289585325463553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 104292235341755576804944565 9777397063289585325463553)
    ·
      refine ⟨7333047797467188994097665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9777397063289585325463553 7333047797467188994097665)
      ·
        refine ⟨5499785848100391745573249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7333047797467188994097665 5499785848100391745573249)
        ·
          refine ⟨4124839386075293809179937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5499785848100391745573249 4124839386075293809179937)
          ·
            refine ⟨3093629539556470356884953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4124839386075293809179937 3093629539556470356884953)
            ·
              refine ⟨2320222154667352767663715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3093629539556470356884953 2320222154667352767663715)
              ·
                refine ⟨3480333232001029151495573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2320222154667352767663715 3480333232001029151495573)
                ·
                  refine ⟨163140620250048241476355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3480333232001029151495573 163140620250048241476355)
                  ·
                    rfl

theorem cell23_2859437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 2, 1, 6].length) (baseStart_2859437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2859437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2859437 prefixEnd_2859437 := by exact prefixLift 2859437
  have htrace : WordTrace (prefixWord ++ tailWord_2859437) baseStart_2859437 baseEnd_2859437 := by
    simpa [prefixWord, tailWord_2859437, baseEnd_2859437] using wordTrace_append hprefix tailTrace_2859437
  have hstable : (prefixWord ++ tailWord_2859437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859437).length < 2 ^ (prefixWord ++ tailWord_2859437).sum := by decide
  have hdescent : baseEnd_2859437 < baseStart_2859437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859453 : List Nat := [1, 4, 1, 2, 2, 3, 1, 1, 3, 1, 4]
def baseStart_2859453 : Nat := 118140960795 + 2859453 * 2 ^ 59
def prefixEnd_2859453 : Nat := 4983230072969 + 3 ^ 40 * 2859453 * 2
def baseEnd_2859453 : Nat := 1468273797940906110687121

theorem tailTrace_2859453 : CollatzResearch.WordTrace tailWord_2859453 prefixEnd_2859453 1468273797940906110687121 := by
  unfold tailWord_2859453
  simp only [CollatzResearch.WordTrace]
  refine ⟨104292818909697611537527013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69528545939798407691684675 104292818909697611537527013)
  ·
    refine ⟨19554903545568302163286315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104292818909697611537527013 19554903545568302163286315)
    ·
      refine ⟨29332355318352453244929473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19554903545568302163286315 29332355318352453244929473)
      ·
        refine ⟨21999266488764339933697105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29332355318352453244929473 21999266488764339933697105)
        ·
          refine ⟨16499449866573254950272829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21999266488764339933697105 16499449866573254950272829)
          ·
            refine ⟨6187293699964970606352311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16499449866573254950272829 6187293699964970606352311)
            ·
              refine ⟨9280940549947455909528467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6187293699964970606352311 9280940549947455909528467)
              ·
                refine ⟨13921410824921183864292701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9280940549947455909528467 13921410824921183864292701)
                ·
                  refine ⟨5220529059345443949109763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13921410824921183864292701 5220529059345443949109763)
                  ·
                    refine ⟨7830793589018165923664645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5220529059345443949109763 7830793589018165923664645)
                    ·
                      refine ⟨1468273797940906110687121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7830793589018165923664645 1468273797940906110687121)
                      ·
                        rfl

theorem cell23_2859453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_2859453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2859453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2859453 prefixEnd_2859453 := by exact prefixLift 2859453
  have htrace : WordTrace (prefixWord ++ tailWord_2859453) baseStart_2859453 baseEnd_2859453 := by
    simpa [prefixWord, tailWord_2859453, baseEnd_2859453] using wordTrace_append hprefix tailTrace_2859453
  have hstable : (prefixWord ++ tailWord_2859453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859453).length < 2 ^ (prefixWord ++ tailWord_2859453).sum := by decide
  have hdescent : baseEnd_2859453 < baseStart_2859453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859473 : List Nat := [1, 2, 2, 1, 2, 1, 1, 7, 1, 2, 3]
def baseStart_2859473 : Nat := 118140960795 + 2859473 * 2 ^ 59
def prefixEnd_2859473 : Nat := 4983230072969 + 3 ^ 40 * 2859473 * 2
def baseEnd_2859473 : Nat := 1468284067553996032437029

theorem tailTrace_2859473 : CollatzResearch.WordTrace tailWord_2859473 prefixEnd_2859473 1468284067553996032437029 := by
  unfold tailWord_2859473
  simp only [CollatzResearch.WordTrace]
  refine ⟨104293548369625154953255073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69529032246416769968836715 104293548369625154953255073)
  ·
    refine ⟨78220161277218866214941305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104293548369625154953255073 78220161277218866214941305)
    ·
      refine ⟨58665120957914149661205979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78220161277218866214941305 58665120957914149661205979)
      ·
        refine ⟨87997681436871224491808969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58665120957914149661205979 87997681436871224491808969)
        ·
          refine ⟨65998261077653418368856727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87997681436871224491808969 65998261077653418368856727)
          ·
            refine ⟨98997391616480127553285091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65998261077653418368856727 98997391616480127553285091)
            ·
              refine ⟨148496087424720191329927637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98997391616480127553285091 148496087424720191329927637)
              ·
                refine ⟨3480377049016879484295179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 148496087424720191329927637 3480377049016879484295179)
                ·
                  refine ⟨5220565573525319226442769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3480377049016879484295179 5220565573525319226442769)
                  ·
                    refine ⟨3915424180143989419832077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5220565573525319226442769 3915424180143989419832077)
                    ·
                      refine ⟨1468284067553996032437029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3915424180143989419832077 1468284067553996032437029)
                      ·
                        rfl

theorem cell23_2859473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 7, 1, 2, 3].length) (baseStart_2859473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2859473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2859473 prefixEnd_2859473 := by exact prefixLift 2859473
  have htrace : WordTrace (prefixWord ++ tailWord_2859473) baseStart_2859473 baseEnd_2859473 := by
    simpa [prefixWord, tailWord_2859473, baseEnd_2859473] using wordTrace_append hprefix tailTrace_2859473
  have hstable : (prefixWord ++ tailWord_2859473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859473).length < 2 ^ (prefixWord ++ tailWord_2859473).sum := by decide
  have hdescent : baseEnd_2859473 < baseStart_2859473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859476 : List Nat := [2, 4, 1, 2, 2, 12]
def baseStart_2859476 : Nat := 118140960795 + 2859476 * 2 ^ 59
def prefixEnd_2859476 : Nat := 4983230072969 + 3 ^ 40 * 2859476 * 2
def baseEnd_2859476 : Nat := 6042327604921644118105

theorem tailTrace_2859476 : CollatzResearch.WordTrace tailWord_2859476 prefixEnd_2859476 6042327604921644118105 := by
  unfold tailWord_2859476
  simp only [CollatzResearch.WordTrace]
  refine ⟨52146828894307143232807141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69529105192409524310409521 52146828894307143232807141)
  ·
    refine ⟨9777530417682589356151339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52146828894307143232807141 9777530417682589356151339)
    ·
      refine ⟨14666295626523884034227009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9777530417682589356151339 14666295626523884034227009)
      ·
        refine ⟨10999721719892913025670257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14666295626523884034227009 10999721719892913025670257)
        ·
          refine ⟨8249791289919684769252693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10999721719892913025670257 8249791289919684769252693)
          ·
            refine ⟨6042327604921644118105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 8249791289919684769252693 6042327604921644118105)
            ·
              rfl

theorem cell23_2859476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 12].length) (baseStart_2859476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2859476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2859476 prefixEnd_2859476 := by exact prefixLift 2859476
  have htrace : WordTrace (prefixWord ++ tailWord_2859476) baseStart_2859476 baseEnd_2859476 := by
    simpa [prefixWord, tailWord_2859476, baseEnd_2859476] using wordTrace_append hprefix tailTrace_2859476
  have hstable : (prefixWord ++ tailWord_2859476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859476).length < 2 ^ (prefixWord ++ tailWord_2859476).sum := by decide
  have hdescent : baseEnd_2859476 < baseStart_2859476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859503 : List Nat := [1, 1, 2, 1, 4, 1, 1, 2, 6, 1, 3]
def baseStart_2859503 : Nat := 118140960795 + 2859503 * 2 ^ 59
def prefixEnd_2859503 : Nat := 4983230072969 + 3 ^ 40 * 2859503 * 2
def baseEnd_2859503 : Nat := 1468299471973630915061891

theorem tailTrace_2859503 : CollatzResearch.WordTrace tailWord_2859503 prefixEnd_2859503 1468299471973630915061891 := by
  unfold tailWord_2859503
  simp only [CollatzResearch.WordTrace]
  refine ⟨104294642559516470076847163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69529761706344313384564775 104294642559516470076847163)
  ·
    refine ⟨156441963839274705115270745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104294642559516470076847163 156441963839274705115270745)
    ·
      refine ⟨117331472879456028836453059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156441963839274705115270745 117331472879456028836453059)
      ·
        refine ⟨175997209319184043254679589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117331472879456028836453059 175997209319184043254679589)
        ·
          refine ⟨32999476747347008110252423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 175997209319184043254679589 32999476747347008110252423)
          ·
            refine ⟨49499215121020512165378635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32999476747347008110252423 49499215121020512165378635)
            ·
              refine ⟨74248822681530768248067953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49499215121020512165378635 74248822681530768248067953)
              ·
                refine ⟨55686617011148076186050965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74248822681530768248067953 55686617011148076186050965)
                ·
                  refine ⟨2610310172397566071221139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 55686617011148076186050965 2610310172397566071221139)
                  ·
                    refine ⟨3915465258596349106831709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2610310172397566071221139 3915465258596349106831709)
                    ·
                      refine ⟨1468299471973630915061891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3915465258596349106831709 1468299471973630915061891)
                      ·
                        rfl

theorem cell23_2859503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 6, 1, 3].length) (baseStart_2859503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2859503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2859503 prefixEnd_2859503 := by exact prefixLift 2859503
  have htrace : WordTrace (prefixWord ++ tailWord_2859503) baseStart_2859503 baseEnd_2859503 := by
    simpa [prefixWord, tailWord_2859503, baseEnd_2859503] using wordTrace_append hprefix tailTrace_2859503
  have hstable : (prefixWord ++ tailWord_2859503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859503).length < 2 ^ (prefixWord ++ tailWord_2859503).sum := by decide
  have hdescent : baseEnd_2859503 < baseStart_2859503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859516 : List Nat := [2, 2, 2, 1, 2, 1, 1, 3, 2, 2, 5]
def baseStart_2859516 : Nat := 118140960795 + 2859516 * 2 ^ 59
def prefixEnd_2859516 : Nat := 4983230072969 + 3 ^ 40 * 2859516 * 2
def baseEnd_2859516 : Nat := 1468306147222139364199331

theorem tailTrace_2859516 : CollatzResearch.WordTrace tailWord_2859516 prefixEnd_2859516 1468306147222139364199331 := by
  unfold tailWord_2859516
  simp only [CollatzResearch.WordTrace]
  refine ⟨52147558354234686648535201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69530077805646248864713601 52147558354234686648535201)
  ·
    refine ⟨39110668765676014986401401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52147558354234686648535201 39110668765676014986401401)
    ·
      refine ⟨29333001574257011239801051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39110668765676014986401401 29333001574257011239801051)
      ·
        refine ⟨43999502361385516859701577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29333001574257011239801051 43999502361385516859701577)
        ·
          refine ⟨32999626771039137644776183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43999502361385516859701577 32999626771039137644776183)
          ·
            refine ⟨49499440156558706467164275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32999626771039137644776183 49499440156558706467164275)
            ·
              refine ⟨74249160234838059700746413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49499440156558706467164275 74249160234838059700746413)
              ·
                refine ⟨27843435088064272387779905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74249160234838059700746413 27843435088064272387779905)
                ·
                  refine ⟨20882576316048204290834929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27843435088064272387779905 20882576316048204290834929)
                  ·
                    refine ⟨15661932237036153218126197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20882576316048204290834929 15661932237036153218126197)
                    ·
                      refine ⟨1468306147222139364199331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15661932237036153218126197 1468306147222139364199331)
                      ·
                        rfl

theorem cell23_2859516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_2859516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2859516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2859516 prefixEnd_2859516 := by exact prefixLift 2859516
  have htrace : WordTrace (prefixWord ++ tailWord_2859516) baseStart_2859516 baseEnd_2859516 := by
    simpa [prefixWord, tailWord_2859516, baseEnd_2859516] using wordTrace_append hprefix tailTrace_2859516
  have hstable : (prefixWord ++ tailWord_2859516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859516).length < 2 ^ (prefixWord ++ tailWord_2859516).sum := by decide
  have hdescent : baseEnd_2859516 < baseStart_2859516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859524 : List Nat := [2, 3, 2, 3, 1, 3, 2, 1, 1, 2, 3]
def baseStart_2859524 : Nat := 118140960795 + 2859524 * 2 ^ 59
def prefixEnd_2859524 : Nat := 4983230072969 + 3 ^ 40 * 2859524 * 2
def baseEnd_2859524 : Nat := 1468310255067375332899295

theorem tailTrace_2859524 : CollatzResearch.WordTrace tailWord_2859524 prefixEnd_2859524 1468310255067375332899295 := by
  unfold tailWord_2859524
  simp only [CollatzResearch.WordTrace]
  refine ⟨52147704246220195331680813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69530272328293593775574417 52147704246220195331680813)
  ·
    refine ⟨19555389092332573249380305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52147704246220195331680813 19555389092332573249380305)
    ·
      refine ⟨14666541819249429937035229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19555389092332573249380305 14666541819249429937035229)
      ·
        refine ⟨5499953182218536226388211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14666541819249429937035229 5499953182218536226388211)
        ·
          refine ⟨8249929773327804339582317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5499953182218536226388211 8249929773327804339582317)
          ·
            refine ⟨3093723664997926627343369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8249929773327804339582317 3093723664997926627343369)
            ·
              refine ⟨2320292748748444970507527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3093723664997926627343369 2320292748748444970507527)
              ·
                refine ⟨3480439123122667455761291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2320292748748444970507527 3480439123122667455761291)
                ·
                  refine ⟨5220658684684001183641937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3480439123122667455761291 5220658684684001183641937)
                  ·
                    refine ⟨3915494013513000887731453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5220658684684001183641937 3915494013513000887731453)
                    ·
                      refine ⟨1468310255067375332899295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3915494013513000887731453 1468310255067375332899295)
                      ·
                        rfl

theorem cell23_2859524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_2859524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2859524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2859524 prefixEnd_2859524 := by exact prefixLift 2859524
  have htrace : WordTrace (prefixWord ++ tailWord_2859524) baseStart_2859524 baseEnd_2859524 := by
    simpa [prefixWord, tailWord_2859524, baseEnd_2859524] using wordTrace_append hprefix tailTrace_2859524
  have hstable : (prefixWord ++ tailWord_2859524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859524).length < 2 ^ (prefixWord ++ tailWord_2859524).sum := by decide
  have hdescent : baseEnd_2859524 < baseStart_2859524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859630 : List Nat := [4, 1, 2, 2, 2, 1, 1, 3, 2, 5]
def baseStart_2859630 : Nat := 118140960795 + 2859630 * 2 ^ 59
def prefixEnd_2859630 : Nat := 4983230072969 + 3 ^ 40 * 2859630 * 2
def baseEnd_2859630 : Nat := 489454894672250639391269

theorem tailTrace_2859630 : CollatzResearch.WordTrace tailWord_2859630 prefixEnd_2859630 489454894672250639391269 := by
  unfold tailWord_2859630
  simp only [CollatzResearch.WordTrace]
  refine ⟨13037409328757046345840043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69532849753370913844480229 13037409328757046345840043)
  ·
    refine ⟨19556113993135569518760065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13037409328757046345840043 19556113993135569518760065)
    ·
      refine ⟨14667085494851677139070049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19556113993135569518760065 14667085494851677139070049)
      ·
        refine ⟨11000314121138757854302537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14667085494851677139070049 11000314121138757854302537)
        ·
          refine ⟨8250235590854068390726903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11000314121138757854302537 8250235590854068390726903)
          ·
            refine ⟨12375353386281102586090355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8250235590854068390726903 12375353386281102586090355)
            ·
              refine ⟨18563030079421653879135533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12375353386281102586090355 18563030079421653879135533)
              ·
                refine ⟨6961136279783120204675825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18563030079421653879135533 6961136279783120204675825)
                ·
                  refine ⟨5220852209837340153506869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6961136279783120204675825 5220852209837340153506869)
                  ·
                    refine ⟨489454894672250639391269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5220852209837340153506869 489454894672250639391269)
                    ·
                      rfl

theorem cell23_2859630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 3, 2, 5].length) (baseStart_2859630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2859630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2859630 prefixEnd_2859630 := by exact prefixLift 2859630
  have htrace : WordTrace (prefixWord ++ tailWord_2859630) baseStart_2859630 baseEnd_2859630 := by
    simpa [prefixWord, tailWord_2859630, baseEnd_2859630] using wordTrace_append hprefix tailTrace_2859630
  have hstable : (prefixWord ++ tailWord_2859630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859630).length < 2 ^ (prefixWord ++ tailWord_2859630).sum := by decide
  have hdescent : baseEnd_2859630 < baseStart_2859630 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859643 : List Nat := [1, 1, 1, 1, 1, 4, 2, 1, 7, 4]
def baseStart_2859643 : Nat := 118140960795 + 2859643 * 2 ^ 59
def prefixEnd_2859643 : Nat := 4983230072969 + 3 ^ 40 * 2859643 * 2
def baseEnd_2859643 : Nat := 489457119755086789103749

theorem tailTrace_2859643 : CollatzResearch.WordTrace tailWord_2859643 prefixEnd_2859643 489457119755086789103749 := by
  unfold tailWord_2859643
  simp only [CollatzResearch.WordTrace]
  refine ⟨104299748779009273986943583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69533165852672849324629055 104299748779009273986943583)
  ·
    refine ⟨156449623168513910980415375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104299748779009273986943583 156449623168513910980415375)
    ·
      refine ⟨234674434752770866470623063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156449623168513910980415375 234674434752770866470623063)
      ·
        refine ⟨352011652129156299705934595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234674434752770866470623063 352011652129156299705934595)
        ·
          refine ⟨528017478193734449558901893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 352011652129156299705934595 528017478193734449558901893)
          ·
            refine ⟨99003277161325209292294105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 528017478193734449558901893 99003277161325209292294105)
            ·
              refine ⟨74252457870993906969220579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99003277161325209292294105 74252457870993906969220579)
              ·
                refine ⟨111378686806490860453830869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74252457870993906969220579 111378686806490860453830869)
                ·
                  refine ⟨2610437972027129541886661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 111378686806490860453830869 2610437972027129541886661)
                  ·
                    refine ⟨489457119755086789103749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2610437972027129541886661 489457119755086789103749)
                    ·
                      rfl

theorem cell23_2859643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 7, 4].length) (baseStart_2859643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2859643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2859643 prefixEnd_2859643 := by exact prefixLift 2859643
  have htrace : WordTrace (prefixWord ++ tailWord_2859643) baseStart_2859643 baseEnd_2859643 := by
    simpa [prefixWord, tailWord_2859643, baseEnd_2859643] using wordTrace_append hprefix tailTrace_2859643
  have hstable : (prefixWord ++ tailWord_2859643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859643).length < 2 ^ (prefixWord ++ tailWord_2859643).sum := by decide
  have hdescent : baseEnd_2859643 < baseStart_2859643 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859673 : List Nat := [1, 2, 1, 2, 1, 2, 3, 5, 6]
def baseStart_2859673 : Nat := 118140960795 + 2859673 * 2 ^ 59
def prefixEnd_2859673 : Nat := 4983230072969 + 3 ^ 40 * 2859673 * 2
def baseEnd_2859673 : Nat := 163154084853877249992901

theorem tailTrace_2859673 : CollatzResearch.WordTrace tailWord_2859673 prefixEnd_2859673 163154084853877249992901 := by
  unfold tailWord_2859673
  simp only [CollatzResearch.WordTrace]
  refine ⟨104300842968900589110535673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69533895312600392740357115 104300842968900589110535673)
  ·
    refine ⟨78225632226675441832901755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104300842968900589110535673 78225632226675441832901755)
    ·
      refine ⟨117338448340013162749352633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78225632226675441832901755 117338448340013162749352633)
      ·
        refine ⟨88003836255009872062014475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117338448340013162749352633 88003836255009872062014475)
        ·
          refine ⟨132005754382514808093021713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88003836255009872062014475 132005754382514808093021713)
          ·
            refine ⟨99004315786886106069766285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132005754382514808093021713 99004315786886106069766285)
            ·
              refine ⟨37126618420082289776162357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99004315786886106069766285 37126618420082289776162357)
              ·
                refine ⟨3480620476882714666515221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37126618420082289776162357 3480620476882714666515221)
                ·
                  refine ⟨163154084853877249992901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3480620476882714666515221 163154084853877249992901)
                  ·
                    rfl

theorem cell23_2859673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 5, 6].length) (baseStart_2859673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2859673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2859673 prefixEnd_2859673 := by exact prefixLift 2859673
  have htrace : WordTrace (prefixWord ++ tailWord_2859673) baseStart_2859673 baseEnd_2859673 := by
    simpa [prefixWord, tailWord_2859673, baseEnd_2859673] using wordTrace_append hprefix tailTrace_2859673
  have hstable : (prefixWord ++ tailWord_2859673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859673).length < 2 ^ (prefixWord ++ tailWord_2859673).sum := by decide
  have hdescent : baseEnd_2859673 < baseStart_2859673 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859683 : List Nat := [1, 1, 1, 4, 1, 1, 2, 1, 1, 7, 3]
def baseStart_2859683 : Nat := 118140960795 + 2859683 * 2 ^ 59
def prefixEnd_2859683 : Nat := 4983230072969 + 3 ^ 40 * 2859683 * 2
def baseEnd_2859683 : Nat := 1468391898491440210811063

theorem tailTrace_2859683 : CollatzResearch.WordTrace tailWord_2859683 prefixEnd_2859683 1468391898491440210811063 := by
  unfold tailWord_2859683
  simp only [CollatzResearch.WordTrace]
  refine ⟨104301207698864360818399703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69534138465909573878933135 104301207698864360818399703)
  ·
    refine ⟨156451811548296541227599555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104301207698864360818399703 156451811548296541227599555)
    ·
      refine ⟨234677717322444811841399333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156451811548296541227599555 234677717322444811841399333)
      ·
        refine ⟨44002071997958402220262375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 234677717322444811841399333 44002071997958402220262375)
        ·
          refine ⟨66003107996937603330393563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44002071997958402220262375 66003107996937603330393563)
          ·
            refine ⟨99004661995406404995590345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66003107996937603330393563 99004661995406404995590345)
            ·
              refine ⟨74253496496554803746692759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99004661995406404995590345 74253496496554803746692759)
              ·
                refine ⟨111380244744832205620039139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74253496496554803746692759 111380244744832205620039139)
                ·
                  refine ⟨167070367117248308430058709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111380244744832205620039139 167070367117248308430058709)
                  ·
                    refine ⟨3915711729310507228829501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 167070367117248308430058709 3915711729310507228829501)
                    ·
                      refine ⟨1468391898491440210811063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3915711729310507228829501 1468391898491440210811063)
                      ·
                        rfl

theorem cell23_2859683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 7, 3].length) (baseStart_2859683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2859683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2859683 prefixEnd_2859683 := by exact prefixLift 2859683
  have htrace : WordTrace (prefixWord ++ tailWord_2859683) baseStart_2859683 baseEnd_2859683 := by
    simpa [prefixWord, tailWord_2859683, baseEnd_2859683] using wordTrace_append hprefix tailTrace_2859683
  have hstable : (prefixWord ++ tailWord_2859683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859683).length < 2 ^ (prefixWord ++ tailWord_2859683).sum := by decide
  have hdescent : baseEnd_2859683 < baseStart_2859683 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859757 : List Nat := [1, 5, 1, 2, 1, 1, 1, 5, 1, 1, 4]
def baseStart_2859757 : Nat := 118140960795 + 2859757 * 2 ^ 59
def prefixEnd_2859757 : Nat := 4983230072969 + 3 ^ 40 * 2859757 * 2
def baseEnd_2859757 : Nat := 1468429896059872921285723

theorem tailTrace_2859757 : CollatzResearch.WordTrace tailWord_2859757 prefixEnd_2859757 1468429896059872921285723 := by
  unfold tailWord_2859757
  simp only [CollatzResearch.WordTrace]
  refine ⟨104303906700596271456593525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69535937800397514304395683 104303906700596271456593525)
  ·
    refine ⟨9778491253180900449055643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 104303906700596271456593525 9778491253180900449055643)
    ·
      refine ⟨14667736879771350673583465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9778491253180900449055643 14667736879771350673583465)
      ·
        refine ⟨11000802659828513005187599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14667736879771350673583465 11000802659828513005187599)
        ·
          refine ⟨16501203989742769507781399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11000802659828513005187599 16501203989742769507781399)
          ·
            refine ⟨24751805984614154261672099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16501203989742769507781399 24751805984614154261672099)
            ·
              refine ⟨37127708976921231392508149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24751805984614154261672099 37127708976921231392508149)
              ·
                refine ⟨3480722716586365443047639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37127708976921231392508149 3480722716586365443047639)
                ·
                  refine ⟨5221084074879548164571459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3480722716586365443047639 5221084074879548164571459)
                  ·
                    refine ⟨7831626112319322246857189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5221084074879548164571459 7831626112319322246857189)
                    ·
                      refine ⟨1468429896059872921285723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7831626112319322246857189 1468429896059872921285723)
                      ·
                        rfl

theorem cell23_2859757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_2859757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2859757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2859757 prefixEnd_2859757 := by exact prefixLift 2859757
  have htrace : WordTrace (prefixWord ++ tailWord_2859757) baseStart_2859757 baseEnd_2859757 := by
    simpa [prefixWord, tailWord_2859757, baseEnd_2859757] using wordTrace_append hprefix tailTrace_2859757
  have hstable : (prefixWord ++ tailWord_2859757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859757).length < 2 ^ (prefixWord ++ tailWord_2859757).sum := by decide
  have hdescent : baseEnd_2859757 < baseStart_2859757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859760 : List Nat := [2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 5]
def baseStart_2859760 : Nat := 118140960795 + 2859760 * 2 ^ 59
def prefixEnd_2859760 : Nat := 4983230072969 + 3 ^ 40 * 2859760 * 2
def baseEnd_2859760 : Nat := 1468431436501836409548209

theorem tailTrace_2859760 : CollatzResearch.WordTrace tailWord_2859760 prefixEnd_2859760 1468431436501836409548209 := by
  unfold tailWord_2859760
  simp only [CollatzResearch.WordTrace]
  refine ⟨52152008059792701484476367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69536010746390268645968489 52152008059792701484476367)
  ·
    refine ⟨78228012089689052226714551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52152008059792701484476367 78228012089689052226714551)
    ·
      refine ⟨117342018134533578340071827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78228012089689052226714551 117342018134533578340071827)
      ·
        refine ⟨176013027201800367510107741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117342018134533578340071827 176013027201800367510107741)
        ·
          refine ⟨66004885200675137816290403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176013027201800367510107741 66004885200675137816290403)
          ·
            refine ⟨99007327801012706724435605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66004885200675137816290403 99007327801012706724435605)
            ·
              refine ⟨4640968490672470627707919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 99007327801012706724435605 4640968490672470627707919)
              ·
                refine ⟨6961452736008705941561879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4640968490672470627707919 6961452736008705941561879)
                ·
                  refine ⟨10442179104013058912342819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6961452736008705941561879 10442179104013058912342819)
                  ·
                    refine ⟨15663268656019588368514229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10442179104013058912342819 15663268656019588368514229)
                    ·
                      refine ⟨1468431436501836409548209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15663268656019588368514229 1468431436501836409548209)
                      ·
                        rfl

theorem cell23_2859760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 5].length) (baseStart_2859760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2859760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2859760 prefixEnd_2859760 := by exact prefixLift 2859760
  have htrace : WordTrace (prefixWord ++ tailWord_2859760) baseStart_2859760 baseEnd_2859760 := by
    simpa [prefixWord, tailWord_2859760, baseEnd_2859760] using wordTrace_append hprefix tailTrace_2859760
  have hstable : (prefixWord ++ tailWord_2859760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859760).length < 2 ^ (prefixWord ++ tailWord_2859760).sum := by decide
  have hdescent : baseEnd_2859760 < baseStart_2859760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859780 : List Nat := [2, 3, 2, 2, 1, 1, 4, 8]
def baseStart_2859780 : Nat := 118140960795 + 2859780 * 2 ^ 59
def prefixEnd_2859780 : Nat := 4983230072969 + 3 ^ 40 * 2859780 * 2
def baseEnd_2859780 : Nat := 54386729856108382640671

theorem tailTrace_2859780 : CollatzResearch.WordTrace tailWord_2859780 prefixEnd_2859780 54386729856108382640671 := by
  unfold tailWord_2859780
  simp only [CollatzResearch.WordTrace]
  refine ⟨52152372789756473192340397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69536497053008630923120529 52152372789756473192340397)
  ·
    refine ⟨19557139796158677447127649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52152372789756473192340397 19557139796158677447127649)
    ·
      refine ⟨14667854847119008085345737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19557139796158677447127649 14667854847119008085345737)
      ·
        refine ⟨11000891135339256064009303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14667854847119008085345737 11000891135339256064009303)
        ·
          refine ⟨16501336703008884096013955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11000891135339256064009303 16501336703008884096013955)
          ·
            refine ⟨24752005054513326144020933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16501336703008884096013955 24752005054513326144020933)
            ·
              refine ⟨4641000947721248652003925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24752005054513326144020933 4641000947721248652003925)
              ·
                refine ⟨54386729856108382640671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4641000947721248652003925 54386729856108382640671)
                ·
                  rfl

theorem cell23_2859780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 8].length) (baseStart_2859780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2859780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2859780 prefixEnd_2859780 := by exact prefixLift 2859780
  have htrace : WordTrace (prefixWord ++ tailWord_2859780) baseStart_2859780 baseEnd_2859780 := by
    simpa [prefixWord, tailWord_2859780, baseEnd_2859780] using wordTrace_append hprefix tailTrace_2859780
  have hstable : (prefixWord ++ tailWord_2859780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859780).length < 2 ^ (prefixWord ++ tailWord_2859780).sum := by decide
  have hdescent : baseEnd_2859780 < baseStart_2859780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859784 : List Nat := [2, 1, 3, 2, 2, 2, 4, 1, 2, 4]
def baseStart_2859784 : Nat := 118140960795 + 2859784 * 2 ^ 59
def prefixEnd_2859784 : Nat := 4983230072969 + 3 ^ 40 * 2859784 * 2
def baseEnd_2859784 : Nat := 489481253345848105216033

theorem tailTrace_2859784 : CollatzResearch.WordTrace tailWord_2859784 prefixEnd_2859784 489481253345848105216033 := by
  unfold tailWord_2859784
  simp only [CollatzResearch.WordTrace]
  refine ⟨52152445735749227533913203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69536594314332303378550937 52152445735749227533913203)
  ·
    refine ⟨78228668603623841300869805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52152445735749227533913203 78228668603623841300869805)
    ·
      refine ⟨29335750726358940487826177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78228668603623841300869805 29335750726358940487826177)
      ·
        refine ⟨22001813044769205365869633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29335750726358940487826177 22001813044769205365869633)
        ·
          refine ⟨16501359783576904024402225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22001813044769205365869633 16501359783576904024402225)
          ·
            refine ⟨12376019837682678018301669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16501359783576904024402225 12376019837682678018301669)
            ·
              refine ⟨2320503719565502128431563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12376019837682678018301669 2320503719565502128431563)
              ·
                refine ⟨3480755579348253192647345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2320503719565502128431563 3480755579348253192647345)
                ·
                  refine ⟨2610566684511189894485509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3480755579348253192647345 2610566684511189894485509)
                  ·
                    refine ⟨489481253345848105216033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2610566684511189894485509 489481253345848105216033)
                    ·
                      rfl

theorem cell23_2859784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 4, 1, 2, 4].length) (baseStart_2859784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2859784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2859784 prefixEnd_2859784 := by exact prefixLift 2859784
  have htrace : WordTrace (prefixWord ++ tailWord_2859784) baseStart_2859784 baseEnd_2859784 := by
    simpa [prefixWord, tailWord_2859784, baseEnd_2859784] using wordTrace_append hprefix tailTrace_2859784
  have hstable : (prefixWord ++ tailWord_2859784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859784).length < 2 ^ (prefixWord ++ tailWord_2859784).sum := by decide
  have hdescent : baseEnd_2859784 < baseStart_2859784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859807 : List Nat := [1, 1, 2, 4, 2, 3, 1, 2, 1, 3, 3]
def baseStart_2859807 : Nat := 118140960795 + 2859807 * 2 ^ 59
def prefixEnd_2859807 : Nat := 4983230072969 + 3 ^ 40 * 2859807 * 2
def baseEnd_2859807 : Nat := 1468455570092597725660493

theorem tailTrace_2859807 : CollatzResearch.WordTrace tailWord_2859807 prefixEnd_2859807 1468455570092597725660493 := by
  unfold tailWord_2859807
  simp only [CollatzResearch.WordTrace]
  refine ⟨104305730350415129995913675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69537153566943419997275783 104305730350415129995913675)
  ·
    refine ⟨156458595525622694993870513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104305730350415129995913675 156458595525622694993870513)
    ·
      refine ⟨117343946644217021245402885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156458595525622694993870513 117343946644217021245402885)
      ·
        refine ⟨22001989995790691483513041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 117343946644217021245402885 22001989995790691483513041)
        ·
          refine ⟨16501492496843018612634781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22001989995790691483513041 16501492496843018612634781)
          ·
            refine ⟨6188059686316131979738043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16501492496843018612634781 6188059686316131979738043)
            ·
              refine ⟨9282089529474197969607065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6188059686316131979738043 9282089529474197969607065)
              ·
                refine ⟨6961567147105648477205299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9282089529474197969607065 6961567147105648477205299)
                ·
                  refine ⟨10442350720658472715807949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6961567147105648477205299 10442350720658472715807949)
                  ·
                    refine ⟨3915881520246927268427981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10442350720658472715807949 3915881520246927268427981)
                    ·
                      refine ⟨1468455570092597725660493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3915881520246927268427981 1468455570092597725660493)
                      ·
                        rfl

theorem cell23_2859807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 2, 1, 3, 3].length) (baseStart_2859807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2859807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2859807 prefixEnd_2859807 := by exact prefixLift 2859807
  have htrace : WordTrace (prefixWord ++ tailWord_2859807) baseStart_2859807 baseEnd_2859807 := by
    simpa [prefixWord, tailWord_2859807, baseEnd_2859807] using wordTrace_append hprefix tailTrace_2859807
  have hstable : (prefixWord ++ tailWord_2859807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859807).length < 2 ^ (prefixWord ++ tailWord_2859807).sum := by decide
  have hdescent : baseEnd_2859807 < baseStart_2859807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859841 : List Nat := [1, 2, 5, 3, 1, 1, 2, 1, 1, 3, 3]
def baseStart_2859841 : Nat := 118140960795 + 2859841 * 2 ^ 59
def prefixEnd_2859841 : Nat := 4983230072969 + 3 ^ 40 * 2859841 * 2
def baseEnd_2859841 : Nat := 1468473028434850592635337

theorem tailTrace_2859841 : CollatzResearch.WordTrace tailWord_2859841 prefixEnd_2859841 1468473028434850592635337 := by
  unfold tailWord_2859841
  simp only [CollatzResearch.WordTrace]
  refine ⟨104306970432291953802651377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69537980288194635868434251 104306970432291953802651377)
  ·
    refine ⟨78230227824218965351988533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104306970432291953802651377 78230227824218965351988533)
    ·
      refine ⟨7334083858520528001748925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 78230227824218965351988533 7334083858520528001748925)
      ·
        refine ⟨2750281446945198000655847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7334083858520528001748925 2750281446945198000655847)
        ·
          refine ⟨4125422170417797000983771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2750281446945198000655847 4125422170417797000983771)
          ·
            refine ⟨6188133255626695501475657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4125422170417797000983771 6188133255626695501475657)
            ·
              refine ⟨4641099941720021626106743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6188133255626695501475657 4641099941720021626106743)
              ·
                refine ⟨6961649912580032439160115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4641099941720021626106743 6961649912580032439160115)
                ·
                  refine ⟨10442474868870048658740173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6961649912580032439160115 10442474868870048658740173)
                  ·
                    refine ⟨3915928075826268247027565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10442474868870048658740173 3915928075826268247027565)
                    ·
                      refine ⟨1468473028434850592635337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3915928075826268247027565 1468473028434850592635337)
                      ·
                        rfl

theorem cell23_2859841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_2859841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2859841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2859841 prefixEnd_2859841 := by exact prefixLift 2859841
  have htrace : WordTrace (prefixWord ++ tailWord_2859841) baseStart_2859841 baseEnd_2859841 := by
    simpa [prefixWord, tailWord_2859841, baseEnd_2859841] using wordTrace_append hprefix tailTrace_2859841
  have hstable : (prefixWord ++ tailWord_2859841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859841).length < 2 ^ (prefixWord ++ tailWord_2859841).sum := by decide
  have hdescent : baseEnd_2859841 < baseStart_2859841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859850 : List Nat := [3, 1, 2, 1, 1, 1, 2, 4, 2, 1, 5]
def baseStart_2859850 : Nat := 118140960795 + 2859850 * 2 ^ 59
def prefixEnd_2859850 : Nat := 4983230072969 + 3 ^ 40 * 2859850 * 2
def baseEnd_2859850 : Nat := 1468477649760741057422795

theorem tailTrace_2859850 : CollatzResearch.WordTrace tailWord_2859850 prefixEnd_2859850 1468477649760741057422795 := by
  unfold tailWord_2859850
  simp only [CollatzResearch.WordTrace]
  refine ⟨26076824672314837084932251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69538199126172898893152669 26076824672314837084932251)
  ·
    refine ⟨39115237008472255627398377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26076824672314837084932251 39115237008472255627398377)
    ·
      refine ⟨29336427756354191720548783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39115237008472255627398377 29336427756354191720548783)
      ·
        refine ⟨44004641634531287580823175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29336427756354191720548783 44004641634531287580823175)
        ·
          refine ⟨66006962451796931371234763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44004641634531287580823175 66006962451796931371234763)
          ·
            refine ⟨99010443677695397056852145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66006962451796931371234763 99010443677695397056852145)
            ·
              refine ⟨74257832758271547792639109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99010443677695397056852145 74257832758271547792639109)
              ·
                refine ⟨13923343642175915211119833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74257832758271547792639109 13923343642175915211119833)
                ·
                  refine ⟨10442507731631936408339875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13923343642175915211119833 10442507731631936408339875)
                  ·
                    refine ⟨15663761597447904612509813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10442507731631936408339875 15663761597447904612509813)
                    ·
                      refine ⟨1468477649760741057422795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15663761597447904612509813 1468477649760741057422795)
                      ·
                        rfl

theorem cell23_2859850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 2, 1, 5].length) (baseStart_2859850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2859850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2859850 prefixEnd_2859850 := by exact prefixLift 2859850
  have htrace : WordTrace (prefixWord ++ tailWord_2859850) baseStart_2859850 baseEnd_2859850 := by
    simpa [prefixWord, tailWord_2859850, baseEnd_2859850] using wordTrace_append hprefix tailTrace_2859850
  have hstable : (prefixWord ++ tailWord_2859850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859850).length < 2 ^ (prefixWord ++ tailWord_2859850).sum := by decide
  have hdescent : baseEnd_2859850 < baseStart_2859850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859868 : List Nat := [2, 2, 4, 2, 1, 1, 4, 1, 1, 3, 2]
def baseStart_2859868 : Nat := 118140960795 + 2859868 * 2 ^ 59
def prefixEnd_2859868 : Nat := 4983230072969 + 3 ^ 40 * 2859868 * 2
def baseEnd_2859868 : Nat := 1468486892412521986997713

theorem tailTrace_2859868 : CollatzResearch.WordTrace tailWord_2859868 prefixEnd_2859868 1468486892412521986997713 := by
  unfold tailWord_2859868
  simp only [CollatzResearch.WordTrace]
  refine ⟨52153977601597068706942129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69538636802129424942589505 52153977601597068706942129)
  ·
    refine ⟨39115483201197801530206597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52153977601597068706942129 39115483201197801530206597)
    ·
      refine ⟨7334153100224587786913737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39115483201197801530206597 7334153100224587786913737)
      ·
        refine ⟨5500614825168440840185303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7334153100224587786913737 5500614825168440840185303)
        ·
          refine ⟨8250922237752661260277955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5500614825168440840185303 8250922237752661260277955)
          ·
            refine ⟨12376383356628991890416933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8250922237752661260277955 12376383356628991890416933)
            ·
              refine ⟨2320571879367935979453175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12376383356628991890416933 2320571879367935979453175)
              ·
                refine ⟨3480857819051903969179763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2320571879367935979453175 3480857819051903969179763)
                ·
                  refine ⟨5221286728577855953769645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3480857819051903969179763 5221286728577855953769645)
                  ·
                    refine ⟨1957982523216695982663617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5221286728577855953769645 1957982523216695982663617)
                    ·
                      refine ⟨1468486892412521986997713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1957982523216695982663617 1468486892412521986997713)
                      ·
                        rfl

theorem cell23_2859868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_2859868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2859868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2859868 prefixEnd_2859868 := by exact prefixLift 2859868
  have htrace : WordTrace (prefixWord ++ tailWord_2859868) baseStart_2859868 baseEnd_2859868 := by
    simpa [prefixWord, tailWord_2859868, baseEnd_2859868] using wordTrace_append hprefix tailTrace_2859868
  have hstable : (prefixWord ++ tailWord_2859868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859868).length < 2 ^ (prefixWord ++ tailWord_2859868).sum := by decide
  have hdescent : baseEnd_2859868 < baseStart_2859868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859894 : List Nat := [5, 1, 1, 3, 1, 1, 2, 1, 2, 2, 4]
def baseStart_2859894 : Nat := 118140960795 + 2859894 * 2 ^ 59
def prefixEnd_2859894 : Nat := 4983230072969 + 3 ^ 40 * 2859894 * 2
def baseEnd_2859894 : Nat := 1468500242909538885272593

theorem tailTrace_2859894 : CollatzResearch.WordTrace tailWord_2859894 prefixEnd_2859894 1468500242909538885272593 := by
  unfold tailWord_2859894
  simp only [CollatzResearch.WordTrace]
  refine ⟨6519306468818746490895671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69539269000733295902887157 6519306468818746490895671)
  ·
    refine ⟨9778959703228119736343507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6519306468818746490895671 9778959703228119736343507)
    ·
      refine ⟨14668439554842179604515261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9778959703228119736343507 14668439554842179604515261)
      ·
        refine ⟨5500664833065817351693223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14668439554842179604515261 5500664833065817351693223)
        ·
          refine ⟨8250997249598726027539835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5500664833065817351693223 8250997249598726027539835)
          ·
            refine ⟨12376495874398089041309753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8250997249598726027539835 12376495874398089041309753)
            ·
              refine ⟨9282371905798566780982315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12376495874398089041309753 9282371905798566780982315)
              ·
                refine ⟨13923557858697850171473473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9282371905798566780982315 13923557858697850171473473)
                ·
                  refine ⟨10442668394023387628605105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13923557858697850171473473 10442668394023387628605105)
                  ·
                    refine ⟨7832001295517540721453829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10442668394023387628605105 7832001295517540721453829)
                    ·
                      refine ⟨1468500242909538885272593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7832001295517540721453829 1468500242909538885272593)
                      ·
                        rfl

theorem cell23_2859894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_2859894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2859894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2859894 prefixEnd_2859894 := by exact prefixLift 2859894
  have htrace : WordTrace (prefixWord ++ tailWord_2859894) baseStart_2859894 baseEnd_2859894 := by
    simpa [prefixWord, tailWord_2859894, baseEnd_2859894] using wordTrace_append hprefix tailTrace_2859894
  have hstable : (prefixWord ++ tailWord_2859894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859894).length < 2 ^ (prefixWord ++ tailWord_2859894).sum := by decide
  have hdescent : baseEnd_2859894 < baseStart_2859894 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859897 : List Nat := [1, 2, 1, 3, 2, 3, 2, 1, 2, 3, 3]
def baseStart_2859897 : Nat := 118140960795 + 2859897 * 2 ^ 59
def prefixEnd_2859897 : Nat := 4983230072969 + 3 ^ 40 * 2859897 * 2
def baseEnd_2859897 : Nat := 1468501783351502373535079

theorem tailTrace_2859897 : CollatzResearch.WordTrace tailWord_2859897 prefixEnd_2859897 1468501783351502373535079 := by
  unfold tailWord_2859897
  simp only [CollatzResearch.WordTrace]
  refine ⟨104309012920089075366689945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69539341946726050244459963 104309012920089075366689945)
  ·
    refine ⟨78231759690066806525017459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104309012920089075366689945 78231759690066806525017459)
    ·
      refine ⟨117347639535100209787526189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78231759690066806525017459 117347639535100209787526189)
      ·
        refine ⟨44005364825662578670322321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117347639535100209787526189 44005364825662578670322321)
        ·
          refine ⟨33004023619246934002741741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44005364825662578670322321 33004023619246934002741741)
          ·
            refine ⟨12376508857217600251028153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33004023619246934002741741 12376508857217600251028153)
            ·
              refine ⟨9282381642913200188271115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12376508857217600251028153 9282381642913200188271115)
              ·
                refine ⟨13923572464369800282406673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9282381642913200188271115 13923572464369800282406673)
                ·
                  refine ⟨10442679348277350211805005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13923572464369800282406673 10442679348277350211805005)
                  ·
                    refine ⟨3916004755604006329426877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10442679348277350211805005 3916004755604006329426877)
                    ·
                      refine ⟨1468501783351502373535079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3916004755604006329426877 1468501783351502373535079)
                      ·
                        rfl

theorem cell23_2859897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 2, 3, 3].length) (baseStart_2859897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2859897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2859897 prefixEnd_2859897 := by exact prefixLift 2859897
  have htrace : WordTrace (prefixWord ++ tailWord_2859897) baseStart_2859897 baseEnd_2859897 := by
    simpa [prefixWord, tailWord_2859897, baseEnd_2859897] using wordTrace_append hprefix tailTrace_2859897
  have hstable : (prefixWord ++ tailWord_2859897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859897).length < 2 ^ (prefixWord ++ tailWord_2859897).sum := by decide
  have hdescent : baseEnd_2859897 < baseStart_2859897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859920 : List Nat := [2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 4]
def baseStart_2859920 : Nat := 118140960795 + 2859920 * 2 ^ 59
def prefixEnd_2859920 : Nat := 4983230072969 + 3 ^ 40 * 2859920 * 2
def baseEnd_2859920 : Nat := 1468513593406555783547473

theorem tailTrace_2859920 : CollatzResearch.WordTrace tailWord_2859920 prefixEnd_2859920 1468513593406555783547473 := by
  unfold tailWord_2859920
  simp only [CollatzResearch.WordTrace]
  refine ⟨52154925899502875147388607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69539901199337166863184809 52154925899502875147388607)
  ·
    refine ⟨78232388849254312721082911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52154925899502875147388607 78232388849254312721082911)
    ·
      refine ⟨117348583273881469081624367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78232388849254312721082911 117348583273881469081624367)
      ·
        refine ⟨176022874910822203622436551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117348583273881469081624367 176022874910822203622436551)
        ·
          refine ⟨264034312366233305433654827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176022874910822203622436551 264034312366233305433654827)
          ·
            refine ⟨396051468549349958150482241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264034312366233305433654827 396051468549349958150482241)
            ·
              refine ⟨297038601412012468612861681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 396051468549349958150482241 297038601412012468612861681)
              ·
                refine ⟨222778951059009351459646261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 297038601412012468612861681 222778951059009351459646261)
                ·
                  refine ⟨20885526661782126699341837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 222778951059009351459646261 20885526661782126699341837)
                  ·
                    refine ⟨7832072498168297512253189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20885526661782126699341837 7832072498168297512253189)
                    ·
                      refine ⟨1468513593406555783547473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7832072498168297512253189 1468513593406555783547473)
                      ·
                        rfl

theorem cell23_2859920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 4].length) (baseStart_2859920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2859920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2859920 prefixEnd_2859920 := by exact prefixLift 2859920
  have htrace : WordTrace (prefixWord ++ tailWord_2859920) baseStart_2859920 baseEnd_2859920 := by
    simpa [prefixWord, tailWord_2859920, baseEnd_2859920] using wordTrace_append hprefix tailTrace_2859920
  have hstable : (prefixWord ++ tailWord_2859920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859920).length < 2 ^ (prefixWord ++ tailWord_2859920).sum := by decide
  have hdescent : baseEnd_2859920 < baseStart_2859920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859949 : List Nat := [1, 5, 2, 3, 2, 1, 2, 1, 2, 2, 2]
def baseStart_2859949 : Nat := 118140960795 + 2859949 * 2 ^ 59
def prefixEnd_2859949 : Nat := 4983230072969 + 3 ^ 40 * 2859949 * 2
def baseEnd_2859949 : Nat := 1468528484345536170084841

theorem tailTrace_2859949 : CollatzResearch.WordTrace tailWord_2859949 prefixEnd_2859949 1468528484345536170084841 := by
  unfold tailWord_2859949
  simp only [CollatzResearch.WordTrace]
  refine ⟨104310909515900688247582901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69540606343933792165055267 104310909515900688247582901)
  ·
    refine ⟨9779147767115689523210897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 104310909515900688247582901 9779147767115689523210897)
    ·
      refine ⟨7334360825336767142408173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9779147767115689523210897 7334360825336767142408173)
      ·
        refine ⟨2750385309501287678403065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7334360825336767142408173 2750385309501287678403065)
        ·
          refine ⟨2062788982125965758802299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2750385309501287678403065 2062788982125965758802299)
          ·
            refine ⟨3094183473188948638203449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2062788982125965758802299 3094183473188948638203449)
            ·
              refine ⟨2320637604891711478652587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3094183473188948638203449 2320637604891711478652587)
              ·
                refine ⟨3480956407337567217978881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2320637604891711478652587 3480956407337567217978881)
                ·
                  refine ⟨2610717305503175413484161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3480956407337567217978881 2610717305503175413484161)
                  ·
                    refine ⟨1958037979127381560113121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2610717305503175413484161 1958037979127381560113121)
                    ·
                      refine ⟨1468528484345536170084841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1958037979127381560113121 1468528484345536170084841)
                      ·
                        rfl

theorem cell23_2859949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_2859949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2859949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2859949 prefixEnd_2859949 := by exact prefixLift 2859949
  have htrace : WordTrace (prefixWord ++ tailWord_2859949) baseStart_2859949 baseEnd_2859949 := by
    simpa [prefixWord, tailWord_2859949, baseEnd_2859949] using wordTrace_append hprefix tailTrace_2859949
  have hstable : (prefixWord ++ tailWord_2859949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859949).length < 2 ^ (prefixWord ++ tailWord_2859949).sum := by decide
  have hdescent : baseEnd_2859949 < baseStart_2859949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2859994 : List Nat := [3, 1, 1, 2, 4, 2, 2, 2, 6]
def baseStart_2859994 : Nat := 118140960795 + 2859994 * 2 ^ 59
def prefixEnd_2859994 : Nat := 4983230072969 + 3 ^ 40 * 2859994 * 2
def baseEnd_2859994 : Nat := 163172398997220943780237

theorem tailTrace_2859994 : CollatzResearch.WordTrace tailWord_2859994 prefixEnd_2859994 163172398997220943780237 := by
  unfold tailWord_2859994
  simp only [CollatzResearch.WordTrace]
  refine ⟨26078137700184415233242759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69541700533825107288647357 26078137700184415233242759)
  ·
    refine ⟨39117206550276622849864139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26078137700184415233242759 39117206550276622849864139)
    ·
      refine ⟨58675809825414934274796209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39117206550276622849864139 58675809825414934274796209)
      ·
        refine ⟨44006857369061200706097157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58675809825414934274796209 44006857369061200706097157)
        ·
          refine ⟨8251285756698975132393217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44006857369061200706097157 8251285756698975132393217)
          ·
            refine ⟨6188464317524231349294913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8251285756698975132393217 6188464317524231349294913)
            ·
              refine ⟨4641348238143173511971185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6188464317524231349294913 4641348238143173511971185)
              ·
                refine ⟨3481011178607380133978389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4641348238143173511971185 3481011178607380133978389)
                ·
                  refine ⟨163172398997220943780237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3481011178607380133978389 163172398997220943780237)
                  ·
                    rfl

theorem cell23_2859994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 2, 6].length) (baseStart_2859994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2859994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2859994 prefixEnd_2859994 := by exact prefixLift 2859994
  have htrace : WordTrace (prefixWord ++ tailWord_2859994) baseStart_2859994 baseEnd_2859994 := by
    simpa [prefixWord, tailWord_2859994, baseEnd_2859994] using wordTrace_append hprefix tailTrace_2859994
  have hstable : (prefixWord ++ tailWord_2859994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2859994).length < 2 ^ (prefixWord ++ tailWord_2859994).sum := by decide
  have hdescent : baseEnd_2859994 < baseStart_2859994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2859994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2860037 : List Nat := [1, 3, 1, 1, 2, 3, 1, 4, 1, 6]
def baseStart_2860037 : Nat := 118140960795 + 2860037 * 2 ^ 59
def prefixEnd_2860037 : Nat := 4983230072969 + 3 ^ 40 * 2860037 * 2
def baseEnd_2860037 : Nat := 489524556881043941928145

theorem tailTrace_2860037 : CollatzResearch.WordTrace tailWord_2860037 prefixEnd_2860037 489524556881043941928145 := by
  unfold tailWord_2860037
  simp only [CollatzResearch.WordTrace]
  refine ⟨104314119139581879276786365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69542746093054586184524243 104314119139581879276786365)
  ·
    refine ⟨39117794677343204728794887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104314119139581879276786365 39117794677343204728794887)
    ·
      refine ⟨58676692016014807093192331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39117794677343204728794887 58676692016014807093192331)
      ·
        refine ⟨88015038024022210639788497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58676692016014807093192331 88015038024022210639788497)
        ·
          refine ⟨66011278518016657979841373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88015038024022210639788497 66011278518016657979841373)
          ·
            refine ⟨24754229444256246742440515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66011278518016657979841373 24754229444256246742440515)
            ·
              refine ⟨37131344166384370113660773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24754229444256246742440515 37131344166384370113660773)
              ·
                refine ⟨6962127031197069396311395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37131344166384370113660773 6962127031197069396311395)
                ·
                  refine ⟨10443190546795604094467093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6962127031197069396311395 10443190546795604094467093)
                  ·
                    refine ⟨489524556881043941928145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10443190546795604094467093 489524556881043941928145)
                    ·
                      rfl

theorem cell23_2860037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 4, 1, 6].length) (baseStart_2860037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2860037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2860037 prefixEnd_2860037 := by exact prefixLift 2860037
  have htrace : WordTrace (prefixWord ++ tailWord_2860037) baseStart_2860037 baseEnd_2860037 := by
    simpa [prefixWord, tailWord_2860037, baseEnd_2860037] using wordTrace_append hprefix tailTrace_2860037
  have hstable : (prefixWord ++ tailWord_2860037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2860037).length < 2 ^ (prefixWord ++ tailWord_2860037).sum := by decide
  have hdescent : baseEnd_2860037 < baseStart_2860037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2860037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2860057 : List Nat := [1, 2, 1, 2, 1, 1, 4, 2, 3, 2, 4]
def baseStart_2860057 : Nat := 118140960795 + 2860057 * 2 ^ 59
def prefixEnd_2860057 : Nat := 4983230072969 + 3 ^ 40 * 2860057 * 2
def baseEnd_2860057 : Nat := 1468583940256221747534343

theorem tailTrace_2860057 : CollatzResearch.WordTrace tailWord_2860057 prefixEnd_2860057 1468583940256221747534343 := by
  unfold tailWord_2860057
  simp only [CollatzResearch.WordTrace]
  refine ⟨104314848599509422692514425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69543232399672948461676283 104314848599509422692514425)
  ·
    refine ⟨78236136449632067019385819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104314848599509422692514425 78236136449632067019385819)
    ·
      refine ⟨117354204674448100529078729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78236136449632067019385819 117354204674448100529078729)
      ·
        refine ⟨88015653505836075396809047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117354204674448100529078729 88015653505836075396809047)
        ·
          refine ⟨132023480258754113095213571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88015653505836075396809047 132023480258754113095213571)
          ·
            refine ⟨198035220388131169642820357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132023480258754113095213571 198035220388131169642820357)
            ·
              refine ⟨37131603822774594308028817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 198035220388131169642820357 37131603822774594308028817)
              ·
                refine ⟨27848702867080945731021613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37131603822774594308028817 27848702867080945731021613)
                ·
                  refine ⟨10443263575155354649133105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27848702867080945731021613 10443263575155354649133105)
                  ·
                    refine ⟨7832447681366515986849829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10443263575155354649133105 7832447681366515986849829)
                    ·
                      refine ⟨1468583940256221747534343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7832447681366515986849829 1468583940256221747534343)
                      ·
                        rfl

theorem cell23_2860057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 3, 2, 4].length) (baseStart_2860057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2860057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2860057 prefixEnd_2860057 := by exact prefixLift 2860057
  have htrace : WordTrace (prefixWord ++ tailWord_2860057) baseStart_2860057 baseEnd_2860057 := by
    simpa [prefixWord, tailWord_2860057, baseEnd_2860057] using wordTrace_append hprefix tailTrace_2860057
  have hstable : (prefixWord ++ tailWord_2860057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2860057).length < 2 ^ (prefixWord ++ tailWord_2860057).sum := by decide
  have hdescent : baseEnd_2860057 < baseStart_2860057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2860057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2860071 : List Nat := [1, 1, 7, 1, 1, 1, 3, 1, 1, 6]
def baseStart_2860071 : Nat := 118140960795 + 2860071 * 2 ^ 59
def prefixEnd_2860071 : Nat := 4983230072969 + 3 ^ 40 * 2860071 * 2
def baseEnd_2860071 : Nat := 489530376328461564253093

theorem tailTrace_2860071 : CollatzResearch.WordTrace tailWord_2860071 prefixEnd_2860071 489530376328461564253093 := by
  unfold tailWord_2860071
  simp only [CollatzResearch.WordTrace]
  refine ⟨104315359221458703083524067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69543572814305802055682711 104315359221458703083524067)
  ·
    refine ⟨156473038832188054625286101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104315359221458703083524067 156473038832188054625286101)
    ·
      refine ⟨3667336847629407530280143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 156473038832188054625286101 3667336847629407530280143)
      ·
        refine ⟨5501005271444111295420215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3667336847629407530280143 5501005271444111295420215)
        ·
          refine ⟨8251507907166166943130323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5501005271444111295420215 8251507907166166943130323)
          ·
            refine ⟨12377261860749250414695485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8251507907166166943130323 12377261860749250414695485)
            ·
              refine ⟨4641473197780968905510807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12377261860749250414695485 4641473197780968905510807)
              ·
                refine ⟨6962209796671453358266211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4641473197780968905510807 6962209796671453358266211)
                ·
                  refine ⟨10443314695007180037399317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6962209796671453358266211 10443314695007180037399317)
                  ·
                    refine ⟨489530376328461564253093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10443314695007180037399317 489530376328461564253093)
                    ·
                      rfl

theorem cell23_2860071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_2860071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2860071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2860071 prefixEnd_2860071 := by exact prefixLift 2860071
  have htrace : WordTrace (prefixWord ++ tailWord_2860071) baseStart_2860071 baseEnd_2860071 := by
    simpa [prefixWord, tailWord_2860071, baseEnd_2860071] using wordTrace_append hprefix tailTrace_2860071
  have hstable : (prefixWord ++ tailWord_2860071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2860071).length < 2 ^ (prefixWord ++ tailWord_2860071).sum := by decide
  have hdescent : baseEnd_2860071 < baseStart_2860071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2860071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2860078 : List Nat := [4, 1, 3, 1, 1, 1, 1, 4, 3, 2, 2]
def baseStart_2860078 : Nat := 118140960795 + 2860078 * 2 ^ 59
def prefixEnd_2860078 : Nat := 4983230072969 + 3 ^ 40 * 2860078 * 2
def baseEnd_2860078 : Nat := 1468594723349966165371747

theorem tailTrace_2860078 : CollatzResearch.WordTrace tailWord_2860078 prefixEnd_2860078 1468594723349966165371747 := by
  unfold tailWord_2860078
  simp only [CollatzResearch.WordTrace]
  refine ⟨13039451816554167909878611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69543743021622228852685925 13039451816554167909878611)
  ·
    refine ⟨19559177724831251864817917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13039451816554167909878611 19559177724831251864817917)
    ·
      refine ⟨7334691646811719449306719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19559177724831251864817917 7334691646811719449306719)
      ·
        refine ⟨11002037470217579173960079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7334691646811719449306719 11002037470217579173960079)
        ·
          refine ⟨16503056205326368760940119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11002037470217579173960079 16503056205326368760940119)
          ·
            refine ⟨24754584307989553141410179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16503056205326368760940119 24754584307989553141410179)
            ·
              refine ⟨37131876461984329712115269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24754584307989553141410179 37131876461984329712115269)
              ·
                refine ⟨6962226836622061821021613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37131876461984329712115269 6962226836622061821021613)
                ·
                  refine ⟨2610835063733273182883105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6962226836622061821021613 2610835063733273182883105)
                  ·
                    refine ⟨1958126297799954887162329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2610835063733273182883105 1958126297799954887162329)
                    ·
                      refine ⟨1468594723349966165371747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1958126297799954887162329 1468594723349966165371747)
                      ·
                        rfl

theorem cell23_2860078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 4, 3, 2, 2].length) (baseStart_2860078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2860078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2860078 prefixEnd_2860078 := by exact prefixLift 2860078
  have htrace : WordTrace (prefixWord ++ tailWord_2860078) baseStart_2860078 baseEnd_2860078 := by
    simpa [prefixWord, tailWord_2860078, baseEnd_2860078] using wordTrace_append hprefix tailTrace_2860078
  have hstable : (prefixWord ++ tailWord_2860078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2860078).length < 2 ^ (prefixWord ++ tailWord_2860078).sum := by decide
  have hdescent : baseEnd_2860078 < baseStart_2860078 := by decide
  rcases family_descends (prefixWord ++ tailWord_2860078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2860081 : List Nat := [1, 2, 2, 3, 1, 2, 4, 2, 1, 2, 3]
def baseStart_2860081 : Nat := 118140960795 + 2860081 * 2 ^ 59
def prefixEnd_2860081 : Nat := 4983230072969 + 3 ^ 40 * 2860081 * 2
def baseEnd_2860081 : Nat := 1468596263791929653634233

theorem tailTrace_2860081 : CollatzResearch.WordTrace tailWord_2860081 prefixEnd_2860081 1468596263791929653634233 := by
  unfold tailWord_2860081
  simp only [CollatzResearch.WordTrace]
  refine ⟨104315723951422474791388097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69543815967614983194258731 104315723951422474791388097)
  ·
    refine ⟨78236792963566856093541073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104315723951422474791388097 78236792963566856093541073)
    ·
      refine ⟨58677594722675142070155805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78236792963566856093541073 58677594722675142070155805)
      ·
        refine ⟨22004098021003178276308427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58677594722675142070155805 22004098021003178276308427)
        ·
          refine ⟨33006147031504767414462641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22004098021003178276308427 33006147031504767414462641)
          ·
            refine ⟨24754610273628575560846981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33006147031504767414462641 24754610273628575560846981)
            ·
              refine ⟨4641489426305357917658809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24754610273628575560846981 4641489426305357917658809)
              ·
                refine ⟨3481117069729018438244107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4641489426305357917658809 3481117069729018438244107)
                ·
                  refine ⟨5221675604593527657366161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3481117069729018438244107 5221675604593527657366161)
                  ·
                    refine ⟨3916256703445145743024621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5221675604593527657366161 3916256703445145743024621)
                    ·
                      refine ⟨1468596263791929653634233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3916256703445145743024621 1468596263791929653634233)
                      ·
                        rfl

theorem cell23_2860081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 2, 1, 2, 3].length) (baseStart_2860081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2860081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2860081 prefixEnd_2860081 := by exact prefixLift 2860081
  have htrace : WordTrace (prefixWord ++ tailWord_2860081) baseStart_2860081 baseEnd_2860081 := by
    simpa [prefixWord, tailWord_2860081, baseEnd_2860081] using wordTrace_append hprefix tailTrace_2860081
  have hstable : (prefixWord ++ tailWord_2860081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2860081).length < 2 ^ (prefixWord ++ tailWord_2860081).sum := by decide
  have hdescent : baseEnd_2860081 < baseStart_2860081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2860081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2860118 : List Nat := [5, 2, 2, 1, 2, 1, 2, 8]
def baseStart_2860118 : Nat := 118140960795 + 2860118 * 2 ^ 59
def prefixEnd_2860118 : Nat := 4983230072969 + 3 ^ 40 * 2860118 * 2
def baseEnd_2860118 : Nat := 54393157873190592921169

theorem tailTrace_2860118 : CollatzResearch.WordTrace tailWord_2860118 prefixEnd_2860118 54393157873190592921169 := by
  unfold tailWord_2860118
  simp only [CollatzResearch.WordTrace]
  refine ⟨6519817090768026881905313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69544715634858953406990005 6519817090768026881905313)
  ·
    refine ⟨4889862818076020161428985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6519817090768026881905313 4889862818076020161428985)
    ·
      refine ⟨3667397113557015121071739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4889862818076020161428985 3667397113557015121071739)
      ·
        refine ⟨5501095670335522681607609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3667397113557015121071739 5501095670335522681607609)
        ·
          refine ⟨4125821752751642011205707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5501095670335522681607609 4125821752751642011205707)
          ·
            refine ⟨6188732629127463016808561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4125821752751642011205707 6188732629127463016808561)
            ·
              refine ⟨4641549471845597262606421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6188732629127463016808561 4641549471845597262606421)
              ·
                refine ⟨54393157873190592921169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4641549471845597262606421 54393157873190592921169)
                ·
                  rfl

theorem cell23_2860118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 8].length) (baseStart_2860118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2860118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2860118 prefixEnd_2860118 := by exact prefixLift 2860118
  have htrace : WordTrace (prefixWord ++ tailWord_2860118) baseStart_2860118 baseEnd_2860118 := by
    simpa [prefixWord, tailWord_2860118, baseEnd_2860118] using wordTrace_append hprefix tailTrace_2860118
  have hstable : (prefixWord ++ tailWord_2860118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2860118).length < 2 ^ (prefixWord ++ tailWord_2860118).sum := by decide
  have hdescent : baseEnd_2860118 < baseStart_2860118 := by decide
  rcases family_descends (prefixWord ++ tailWord_2860118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2860127 : List Nat := [1, 1, 2, 3, 1, 1, 4, 1, 1, 8]
def baseStart_2860127 : Nat := 118140960795 + 2860127 * 2 ^ 59
def prefixEnd_2860127 : Nat := 4983230072969 + 3 ^ 40 * 2860127 * 2
def baseEnd_2860127 : Nat := 489539961300678824553007

theorem tailTrace_2860127 : CollatzResearch.WordTrace tailWord_2860127 prefixEnd_2860127 489539961300678824553007 := by
  unfold tailWord_2860127
  simp only [CollatzResearch.WordTrace]
  refine ⟨104317401709255824647562635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69544934472837216431708423 104317401709255824647562635)
  ·
    refine ⟨156476102563883736971343953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104317401709255824647562635 156476102563883736971343953)
    ·
      refine ⟨117357076922912802728507965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156476102563883736971343953 117357076922912802728507965)
      ·
        refine ⟨44008903846092301023190487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117357076922912802728507965 44008903846092301023190487)
        ·
          refine ⟨66013355769138451534785731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44008903846092301023190487 66013355769138451534785731)
          ·
            refine ⟨99020033653707677302178597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66013355769138451534785731 99020033653707677302178597)
            ·
              refine ⟨18566256310070189494158487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99020033653707677302178597 18566256310070189494158487)
              ·
                refine ⟨27849384465105284241237731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18566256310070189494158487 27849384465105284241237731)
                ·
                  refine ⟨41774076697657926361856597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27849384465105284241237731 41774076697657926361856597)
                  ·
                    refine ⟨489539961300678824553007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 41774076697657926361856597 489539961300678824553007)
                    ·
                      rfl

theorem cell23_2860127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 8].length) (baseStart_2860127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2860127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2860127 prefixEnd_2860127 := by exact prefixLift 2860127
  have htrace : WordTrace (prefixWord ++ tailWord_2860127) baseStart_2860127 baseEnd_2860127 := by
    simpa [prefixWord, tailWord_2860127, baseEnd_2860127] using wordTrace_append hprefix tailTrace_2860127
  have hstable : (prefixWord ++ tailWord_2860127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2860127).length < 2 ^ (prefixWord ++ tailWord_2860127).sum := by decide
  have hdescent : baseEnd_2860127 < baseStart_2860127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2860127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2860138 : List Nat := [3, 1, 3, 2, 2, 2, 1, 1, 3, 3, 2]
def baseStart_2860138 : Nat := 118140960795 + 2860138 * 2 ^ 59
def prefixEnd_2860138 : Nat := 4983230072969 + 3 ^ 40 * 2860138 * 2
def baseEnd_2860138 : Nat := 1468625532189235930621471

theorem tailTrace_2860138 : CollatzResearch.WordTrace tailWord_2860138 prefixEnd_2860138 1468625532189235930621471 := by
  unfold tailWord_2860138
  simp only [CollatzResearch.WordTrace]
  refine ⟨26079450728053993381553267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69545201941477315684142045 26079450728053993381553267)
  ·
    refine ⟨39119176092080990072329901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26079450728053993381553267 39119176092080990072329901)
    ·
      refine ⟨14669691034530371277123713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39119176092080990072329901 14669691034530371277123713)
      ·
        refine ⟨11002268275897778457842785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14669691034530371277123713 11002268275897778457842785)
        ·
          refine ⟨8251701206923333843382089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11002268275897778457842785 8251701206923333843382089)
          ·
            refine ⟨6188775905192500382536567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8251701206923333843382089 6188775905192500382536567)
            ·
              refine ⟨9283163857788750573804851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6188775905192500382536567 9283163857788750573804851)
              ·
                refine ⟨13924745786683125860707277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9283163857788750573804851 13924745786683125860707277)
                ·
                  refine ⟨5221779670006172197765229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13924745786683125860707277 5221779670006172197765229)
                  ·
                    refine ⟨1958167376252314574161961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5221779670006172197765229 1958167376252314574161961)
                    ·
                      refine ⟨1468625532189235930621471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1958167376252314574161961 1468625532189235930621471)
                      ·
                        rfl

theorem cell23_2860138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 3, 3, 2].length) (baseStart_2860138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2860138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2860138 prefixEnd_2860138 := by exact prefixLift 2860138
  have htrace : WordTrace (prefixWord ++ tailWord_2860138) baseStart_2860138 baseEnd_2860138 := by
    simpa [prefixWord, tailWord_2860138, baseEnd_2860138] using wordTrace_append hprefix tailTrace_2860138
  have hstable : (prefixWord ++ tailWord_2860138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2860138).length < 2 ^ (prefixWord ++ tailWord_2860138).sum := by decide
  have hdescent : baseEnd_2860138 < baseStart_2860138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2860138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2860151 : List Nat := [1, 1, 3, 1, 1, 4, 3, 2, 1, 4, 2]
def baseStart_2860151 : Nat := 118140960795 + 2860151 * 2 ^ 59
def prefixEnd_2860151 : Nat := 4983230072969 + 3 ^ 40 * 2860151 * 2
def baseEnd_2860151 : Nat := 1468632207437744379758911

theorem tailTrace_2860151 : CollatzResearch.WordTrace tailWord_2860151 prefixEnd_2860151 1468632207437744379758911 := by
  unfold tailWord_2860151
  simp only [CollatzResearch.WordTrace]
  refine ⟨104318277061168876746436307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69545518040779251164290871 104318277061168876746436307)
  ·
    refine ⟨156477415591753315119654461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104318277061168876746436307 156477415591753315119654461)
    ·
      refine ⟨58679030846907493169870423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156477415591753315119654461 58679030846907493169870423)
      ·
        refine ⟨88018546270361239754805635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58679030846907493169870423 88018546270361239754805635)
        ·
          refine ⟨132027819405541859632208453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88018546270361239754805635 132027819405541859632208453)
          ·
            refine ⟨24755216138539098681039085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 132027819405541859632208453 24755216138539098681039085)
            ·
              refine ⟨9283206051952162005389657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24755216138539098681039085 9283206051952162005389657)
              ·
                refine ⟨6962404538964121504042243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9283206051952162005389657 6962404538964121504042243)
                ·
                  refine ⟨10443606808446182256063365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6962404538964121504042243 10443606808446182256063365)
                  ·
                    refine ⟨1958176276583659173011881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10443606808446182256063365 1958176276583659173011881)
                    ·
                      refine ⟨1468632207437744379758911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1958176276583659173011881 1468632207437744379758911)
                      ·
                        rfl

theorem cell23_2860151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 2, 1, 4, 2].length) (baseStart_2860151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2860151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2860151 prefixEnd_2860151 := by exact prefixLift 2860151
  have htrace : WordTrace (prefixWord ++ tailWord_2860151) baseStart_2860151 baseEnd_2860151 := by
    simpa [prefixWord, tailWord_2860151, baseEnd_2860151] using wordTrace_append hprefix tailTrace_2860151
  have hstable : (prefixWord ++ tailWord_2860151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2860151).length < 2 ^ (prefixWord ++ tailWord_2860151).sum := by decide
  have hdescent : baseEnd_2860151 < baseStart_2860151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2860151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2860191 : List Nat := [1, 1, 2, 6, 2, 1, 1, 2, 7]
def baseStart_2860191 : Nat := 118140960795 + 2860191 * 2 ^ 59
def prefixEnd_2860191 : Nat := 4983230072969 + 3 ^ 40 * 2860191 * 2
def baseEnd_2860191 : Nat := 163183638518213802584303

theorem tailTrace_2860191 : CollatzResearch.WordTrace tailWord_2860191 prefixEnd_2860191 163183638518213802584303 := by
  unfold tailWord_2860191
  simp only [CollatzResearch.WordTrace]
  refine ⟨104319735981023963577892427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69546490654015975718594951 104319735981023963577892427)
  ·
    refine ⟨156479603971535945366838641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104319735981023963577892427 156479603971535945366838641)
    ·
      refine ⟨117359702978651959025128981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156479603971535945366838641 117359702978651959025128981)
      ·
        refine ⟨5501236077124310579302921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 117359702978651959025128981 5501236077124310579302921)
        ·
          refine ⟨4125927057843232934477191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5501236077124310579302921 4125927057843232934477191)
          ·
            refine ⟨6188890586764849401715787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4125927057843232934477191 6188890586764849401715787)
            ·
              refine ⟨9283335880147274102573681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6188890586764849401715787 9283335880147274102573681)
              ·
                refine ⟨6962501910110455576930261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9283335880147274102573681 6962501910110455576930261)
                ·
                  refine ⟨163183638518213802584303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6962501910110455576930261 163183638518213802584303)
                  ·
                    rfl

theorem cell23_2860191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 2, 7].length) (baseStart_2860191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2860191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2860191 prefixEnd_2860191 := by exact prefixLift 2860191
  have htrace : WordTrace (prefixWord ++ tailWord_2860191) baseStart_2860191 baseEnd_2860191 := by
    simpa [prefixWord, tailWord_2860191, baseEnd_2860191] using wordTrace_append hprefix tailTrace_2860191
  have hstable : (prefixWord ++ tailWord_2860191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2860191).length < 2 ^ (prefixWord ++ tailWord_2860191).sum := by decide
  have hdescent : baseEnd_2860191 < baseStart_2860191 := by decide
  rcases family_descends (prefixWord ++ tailWord_2860191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2860204 : List Nat := [2, 2, 1, 1, 1, 1, 1, 7, 2, 5]
def baseStart_2860204 : Nat := 118140960795 + 2860204 * 2 ^ 59
def prefixEnd_2860204 : Nat := 4983230072969 + 3 ^ 40 * 2860204 * 2
def baseEnd_2860204 : Nat := 489553140637477557465389

theorem tailTrace_2860204 : CollatzResearch.WordTrace tailWord_2860204 prefixEnd_2860204 489553140637477557465389 := by
  unfold tailWord_2860204
  simp only [CollatzResearch.WordTrace]
  refine ⟨52160105064988433399057833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69546806753317911198743777 52160105064988433399057833)
  ·
    refine ⟨39120078798741325049293375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52160105064988433399057833 39120078798741325049293375)
    ·
      refine ⟨58680118198111987573940063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39120078798741325049293375 58680118198111987573940063)
      ·
        refine ⟨88020177297167981360910095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58680118198111987573940063 88020177297167981360910095)
        ·
          refine ⟨132030265945751972041365143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88020177297167981360910095 132030265945751972041365143)
          ·
            refine ⟨198045398918627958062047715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132030265945751972041365143 198045398918627958062047715)
            ·
              refine ⟨297068098377941937093071573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198045398918627958062047715 297068098377941937093071573)
              ·
                refine ⟨6962533555733014150618865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 297068098377941937093071573 6962533555733014150618865)
                ·
                  refine ⟨5221900166799760612964149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6962533555733014150618865 5221900166799760612964149)
                  ·
                    refine ⟨489553140637477557465389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5221900166799760612964149 489553140637477557465389)
                    ·
                      rfl

theorem cell23_2860204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 5].length) (baseStart_2860204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2860204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2860204 prefixEnd_2860204 := by exact prefixLift 2860204
  have htrace : WordTrace (prefixWord ++ tailWord_2860204) baseStart_2860204 baseEnd_2860204 := by
    simpa [prefixWord, tailWord_2860204, baseEnd_2860204] using wordTrace_append hprefix tailTrace_2860204
  have hstable : (prefixWord ++ tailWord_2860204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2860204).length < 2 ^ (prefixWord ++ tailWord_2860204).sum := by decide
  have hdescent : baseEnd_2860204 < baseStart_2860204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2860204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2860264 : List Nat := [2, 1, 4, 1, 2, 1, 1, 1, 10]
def baseStart_2860264 : Nat := 118140960795 + 2860264 * 2 ^ 59
def prefixEnd_2860264 : Nat := 4983230072969 + 3 ^ 40 * 2860264 * 2
def baseEnd_2860264 : Nat := 163187803416855826405099

theorem tailTrace_2860264 : CollatzResearch.WordTrace tailWord_2860264 prefixEnd_2860264 163187803416855826405099 := by
  unfold tailWord_2860264
  simp only [CollatzResearch.WordTrace]
  refine ⟨52161199254879748522649923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69548265673172998030199897 52161199254879748522649923)
  ·
    refine ⟨78241798882319622783974885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52161199254879748522649923 78241798882319622783974885)
    ·
      refine ⟨14670337290434929271995291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78241798882319622783974885 14670337290434929271995291)
      ·
        refine ⟨22005505935652393907992937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14670337290434929271995291 22005505935652393907992937)
        ·
          refine ⟨16504129451739295430994703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22005505935652393907992937 16504129451739295430994703)
          ·
            refine ⟨24756194177608943146492055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16504129451739295430994703 24756194177608943146492055)
            ·
              refine ⟨37134291266413414719738083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24756194177608943146492055 37134291266413414719738083)
              ·
                refine ⟨55701436899620122079607125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37134291266413414719738083 55701436899620122079607125)
                ·
                  refine ⟨163187803416855826405099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 55701436899620122079607125 163187803416855826405099)
                  ·
                    rfl

theorem cell23_2860264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 10].length) (baseStart_2860264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2860264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2860264 prefixEnd_2860264 := by exact prefixLift 2860264
  have htrace : WordTrace (prefixWord ++ tailWord_2860264) baseStart_2860264 baseEnd_2860264 := by
    simpa [prefixWord, tailWord_2860264, baseEnd_2860264] using wordTrace_append hprefix tailTrace_2860264
  have hstable : (prefixWord ++ tailWord_2860264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2860264).length < 2 ^ (prefixWord ++ tailWord_2860264).sum := by decide
  have hdescent : baseEnd_2860264 < baseStart_2860264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2860264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2860311 : List Nat := [1, 1, 3, 4, 1, 1, 3, 1, 3, 5]
def baseStart_2860311 : Nat := 118140960795 + 2860311 * 2 ^ 59
def prefixEnd_2860311 : Nat := 4983230072969 + 3 ^ 40 * 2860311 * 2
def baseEnd_2860311 : Nat := 489571454780821251252725

theorem tailTrace_2860311 : CollatzResearch.WordTrace tailWord_2860311 prefixEnd_2860311 489571454780821251252725 := by
  unfold tailWord_2860311
  simp only [CollatzResearch.WordTrace]
  refine ⟨104324112740589224072260787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69549408493726149381507191 104324112740589224072260787)
  ·
    refine ⟨156486169110883836108391181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104324112740589224072260787 156486169110883836108391181)
    ·
      refine ⟨58682313416581438540646693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156486169110883836108391181 58682313416581438540646693)
      ·
        refine ⟨11002933765609019726371255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58682313416581438540646693 11002933765609019726371255)
        ·
          refine ⟨16504400648413529589556883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11002933765609019726371255 16504400648413529589556883)
          ·
            refine ⟨24756600972620294384335325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16504400648413529589556883 24756600972620294384335325)
            ·
              refine ⟨9283725364732610394125747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24756600972620294384335325 9283725364732610394125747)
              ·
                refine ⟨13925588047098915591188621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9283725364732610394125747 13925588047098915591188621)
                ·
                  refine ⟨5222095517662093346695733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13925588047098915591188621 5222095517662093346695733)
                  ·
                    refine ⟨489571454780821251252725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5222095517662093346695733 489571454780821251252725)
                    ·
                      rfl

theorem cell23_2860311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 3, 5].length) (baseStart_2860311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2860311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2860311 prefixEnd_2860311 := by exact prefixLift 2860311
  have htrace : WordTrace (prefixWord ++ tailWord_2860311) baseStart_2860311 baseEnd_2860311 := by
    simpa [prefixWord, tailWord_2860311, baseEnd_2860311] using wordTrace_append hprefix tailTrace_2860311
  have hstable : (prefixWord ++ tailWord_2860311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2860311).length < 2 ^ (prefixWord ++ tailWord_2860311).sum := by decide
  have hdescent : baseEnd_2860311 < baseStart_2860311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2860311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2860331 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 3, 8, 2]
def baseStart_2860331 : Nat := 118140960795 + 2860331 * 2 ^ 59
def prefixEnd_2860331 : Nat := 4983230072969 + 3 ^ 40 * 2860331 * 2
def baseEnd_2860331 : Nat := 1468724633955553675508083

theorem tailTrace_2860331 : CollatzResearch.WordTrace tailWord_2860331 prefixEnd_2860331 1468724633955553675508083 := by
  unfold tailWord_2860331
  simp only [CollatzResearch.WordTrace]
  refine ⟨104324842200516767487988847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69549894800344511658659231 104324842200516767487988847)
  ·
    refine ⟨156487263300775151231983271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104324842200516767487988847 156487263300775151231983271)
    ·
      refine ⟨234730894951162726847974907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156487263300775151231983271 234730894951162726847974907)
      ·
        refine ⟨352096342426744090271962361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234730894951162726847974907 352096342426744090271962361)
        ·
          refine ⟨264072256820058067703971771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 352096342426744090271962361 264072256820058067703971771)
          ·
            refine ⟨396108385230087101555957657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264072256820058067703971771 396108385230087101555957657)
            ·
              refine ⟨297081288922565326166968243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 396108385230087101555957657 297081288922565326166968243)
              ·
                refine ⟨445621933383847989250452365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 297081288922565326166968243 445621933383847989250452365)
                ·
                  refine ⟨167108225018942995968919637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 445621933383847989250452365 167108225018942995968919637)
                  ·
                    refine ⟨1958299511940738234010777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 167108225018942995968919637 1958299511940738234010777)
                    ·
                      refine ⟨1468724633955553675508083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1958299511940738234010777 1468724633955553675508083)
                      ·
                        rfl

theorem cell23_2860331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 8, 2].length) (baseStart_2860331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2860331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2860331 prefixEnd_2860331 := by exact prefixLift 2860331
  have htrace : WordTrace (prefixWord ++ tailWord_2860331) baseStart_2860331 baseEnd_2860331 := by
    simpa [prefixWord, tailWord_2860331, baseEnd_2860331] using wordTrace_append hprefix tailTrace_2860331
  have hstable : (prefixWord ++ tailWord_2860331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2860331).length < 2 ^ (prefixWord ++ tailWord_2860331).sum := by decide
  have hdescent : baseEnd_2860331 < baseStart_2860331 := by decide
  rcases family_descends (prefixWord ++ tailWord_2860331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2860361 : List Nat := [1, 2, 1, 1, 2, 3, 3, 3, 1, 2, 4]
def baseStart_2860361 : Nat := 118140960795 + 2860361 * 2 ^ 59
def prefixEnd_2860361 : Nat := 4983230072969 + 3 ^ 40 * 2860361 * 2
def baseEnd_2860361 : Nat := 1468740038375188558132945

theorem tailTrace_2860361 : CollatzResearch.WordTrace tailWord_2860361 prefixEnd_2860361 1468740038375188558132945 := by
  unfold tailWord_2860361
  simp only [CollatzResearch.WordTrace]
  refine ⟨104325936390408082611580937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69550624260272055074387291 104325936390408082611580937)
  ·
    refine ⟨78244452292806061958685703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104325936390408082611580937 78244452292806061958685703)
    ·
      refine ⟨117366678439209092938028555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78244452292806061958685703 117366678439209092938028555)
      ·
        refine ⟨176050017658813639407042833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117366678439209092938028555 176050017658813639407042833)
        ·
          refine ⟨132037513244110229555282125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176050017658813639407042833 132037513244110229555282125)
          ·
            refine ⟨49514067466541336083230797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132037513244110229555282125 49514067466541336083230797)
            ·
              refine ⟨18567775299953001031211549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49514067466541336083230797 18567775299953001031211549)
              ·
                refine ⟨6962915737482375386704331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18567775299953001031211549 6962915737482375386704331)
                ·
                  refine ⟨10444373606223563080056497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6962915737482375386704331 10444373606223563080056497)
                  ·
                    refine ⟨7833280204667672310042373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10444373606223563080056497 7833280204667672310042373)
                    ·
                      refine ⟨1468740038375188558132945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7833280204667672310042373 1468740038375188558132945)
                      ·
                        rfl

theorem cell23_2860361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 3, 1, 2, 4].length) (baseStart_2860361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2860361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2860361 prefixEnd_2860361 := by exact prefixLift 2860361
  have htrace : WordTrace (prefixWord ++ tailWord_2860361) baseStart_2860361 baseEnd_2860361 := by
    simpa [prefixWord, tailWord_2860361, baseEnd_2860361] using wordTrace_append hprefix tailTrace_2860361
  have hstable : (prefixWord ++ tailWord_2860361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2860361).length < 2 ^ (prefixWord ++ tailWord_2860361).sum := by decide
  have hdescent : baseEnd_2860361 < baseStart_2860361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2860361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2860368 : List Nat := [2, 1, 1, 1, 1, 5, 2, 4, 1, 2, 3]
def baseStart_2860368 : Nat := 118140960795 + 2860368 * 2 ^ 59
def prefixEnd_2860368 : Nat := 4983230072969 + 3 ^ 40 * 2860368 * 2
def baseEnd_2860368 : Nat := 1468743632739770030745413

theorem tailTrace_2860368 : CollatzResearch.WordTrace tailWord_2860368 prefixEnd_2860368 1468743632739770030745413 := by
  unfold tailWord_2860368
  simp only [CollatzResearch.WordTrace]
  refine ⟨52163095850691361403542879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69550794467588481871390505 52163095850691361403542879)
  ·
    refine ⟨78244643776037042105314319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52163095850691361403542879 78244643776037042105314319)
    ·
      refine ⟨117366965664055563157971479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78244643776037042105314319 117366965664055563157971479)
      ·
        refine ⟨176050448496083344736957219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117366965664055563157971479 176050448496083344736957219)
        ·
          refine ⟨264075672744125017105435829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176050448496083344736957219 264075672744125017105435829)
          ·
            refine ⟨24757094319761720353634609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 264075672744125017105435829 24757094319761720353634609)
            ·
              refine ⟨18567820739821290265225957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24757094319761720353634609 18567820739821290265225957)
              ·
                refine ⟨3481466388716491924729867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18567820739821290265225957 3481466388716491924729867)
                ·
                  refine ⟨5222199583074737887094801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3481466388716491924729867 5222199583074737887094801)
                  ·
                    refine ⟨3916649687306053415321101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5222199583074737887094801 3916649687306053415321101)
                    ·
                      refine ⟨1468743632739770030745413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3916649687306053415321101 1468743632739770030745413)
                      ·
                        rfl

theorem cell23_2860368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 4, 1, 2, 3].length) (baseStart_2860368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2860368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2860368 prefixEnd_2860368 := by exact prefixLift 2860368
  have htrace : WordTrace (prefixWord ++ tailWord_2860368) baseStart_2860368 baseEnd_2860368 := by
    simpa [prefixWord, tailWord_2860368, baseEnd_2860368] using wordTrace_append hprefix tailTrace_2860368
  have hstable : (prefixWord ++ tailWord_2860368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2860368).length < 2 ^ (prefixWord ++ tailWord_2860368).sum := by decide
  have hdescent : baseEnd_2860368 < baseStart_2860368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2860368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2860371 : List Nat := [1, 1, 1, 2, 1, 1, 9, 7]
def baseStart_2860371 : Nat := 118140960795 + 2860371 * 2 ^ 59
def prefixEnd_2860371 : Nat := 4983230072969 + 3 ^ 40 * 2860371 * 2
def baseEnd_2860371 : Nat := 54397969377101241444737

theorem tailTrace_2860371 : CollatzResearch.WordTrace tailWord_2860371 prefixEnd_2860371 54397969377101241444737 := by
  unfold tailWord_2860371
  simp only [CollatzResearch.WordTrace]
  refine ⟨104326301120371854319444967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69550867413581236212963311 104326301120371854319444967)
  ·
    refine ⟨156489451680557781479167451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104326301120371854319444967 156489451680557781479167451)
    ·
      refine ⟨234734177520836672218751177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156489451680557781479167451 234734177520836672218751177)
      ·
        refine ⟨176050633140627504164063383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234734177520836672218751177 176050633140627504164063383)
        ·
          refine ⟨264075949710941256246095075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176050633140627504164063383 264075949710941256246095075)
          ·
            refine ⟨396113924566411884369142613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264075949710941256246095075 396113924566411884369142613)
            ·
              refine ⟨2320980026756319634975445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 396113924566411884369142613 2320980026756319634975445)
              ·
                refine ⟨54397969377101241444737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2320980026756319634975445 54397969377101241444737)
                ·
                  rfl

theorem cell23_2860371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 9, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 9, 7].length) (baseStart_2860371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2860371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2860371 prefixEnd_2860371 := by exact prefixLift 2860371
  have htrace : WordTrace (prefixWord ++ tailWord_2860371) baseStart_2860371 baseEnd_2860371 := by
    simpa [prefixWord, tailWord_2860371, baseEnd_2860371] using wordTrace_append hprefix tailTrace_2860371
  have hstable : (prefixWord ++ tailWord_2860371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2860371).length < 2 ^ (prefixWord ++ tailWord_2860371).sum := by decide
  have hdescent : baseEnd_2860371 < baseStart_2860371 := by decide
  rcases family_descends (prefixWord ++ tailWord_2860371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2860392 : List Nat := [2, 1, 4, 2, 3, 2, 1, 2, 2, 4]
def baseStart_2860392 : Nat := 118140960795 + 2860392 * 2 ^ 59
def prefixEnd_2860392 : Nat := 4983230072969 + 3 ^ 40 * 2860392 * 2
def baseEnd_2860392 : Nat := 489585318758492645615101

theorem tailTrace_2860392 : CollatzResearch.WordTrace tailWord_2860392 prefixEnd_2860392 489585318758492645615101 := by
  unfold tailWord_2860392
  simp only [CollatzResearch.WordTrace]
  refine ⟨52163533526647887452979715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69551378035530516603972953 52163533526647887452979715)
  ·
    refine ⟨78245300289971831179469573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52163533526647887452979715 78245300289971831179469573)
    ·
      refine ⟨14670993804369718346150545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78245300289971831179469573 14670993804369718346150545)
      ·
        refine ⟨11003245353277288759612909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14670993804369718346150545 11003245353277288759612909)
        ·
          refine ⟨4126217007478983284854841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11003245353277288759612909 4126217007478983284854841)
          ·
            refine ⟨3094662755609237463641131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4126217007478983284854841 3094662755609237463641131)
            ·
              refine ⟨4641994133413856195461697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3094662755609237463641131 4641994133413856195461697)
              ·
                refine ⟨3481495600060392146596273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4641994133413856195461697 3481495600060392146596273)
                ·
                  refine ⟨2611121700045294109947205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3481495600060392146596273 2611121700045294109947205)
                  ·
                    refine ⟨489585318758492645615101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2611121700045294109947205 489585318758492645615101)
                    ·
                      rfl

theorem cell23_2860392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 2, 2, 4].length) (baseStart_2860392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2860392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2860392 prefixEnd_2860392 := by exact prefixLift 2860392
  have htrace : WordTrace (prefixWord ++ tailWord_2860392) baseStart_2860392 baseEnd_2860392 := by
    simpa [prefixWord, tailWord_2860392, baseEnd_2860392] using wordTrace_append hprefix tailTrace_2860392
  have hstable : (prefixWord ++ tailWord_2860392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2860392).length < 2 ^ (prefixWord ++ tailWord_2860392).sum := by decide
  have hdescent : baseEnd_2860392 < baseStart_2860392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2860392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2860421 : List Nat := [1, 3, 1, 1, 3, 1, 2, 2, 2, 3, 4]
def baseStart_2860421 : Nat := 118140960795 + 2860421 * 2 ^ 59
def prefixEnd_2860421 : Nat := 4983230072969 + 3 ^ 40 * 2860421 * 2
def baseEnd_2860421 : Nat := 1468770847214458323382669

theorem tailTrace_2860421 : CollatzResearch.WordTrace tailWord_2860421 prefixEnd_2860421 1468770847214458323382669 := by
  unfold tailWord_2860421
  simp only [CollatzResearch.WordTrace]
  refine ⟨104328124770190712858765117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69552083180127141905843411 104328124770190712858765117)
  ·
    refine ⟨39123046788821517322036919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104328124770190712858765117 39123046788821517322036919)
    ·
      refine ⟨58684570183232275983055379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39123046788821517322036919 58684570183232275983055379)
      ·
        refine ⟨88026855274848413974583069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58684570183232275983055379 88026855274848413974583069)
        ·
          refine ⟨33010070728068155240468651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88026855274848413974583069 33010070728068155240468651)
          ·
            refine ⟨49515106092102232860702977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33010070728068155240468651 49515106092102232860702977)
            ·
              refine ⟨37136329569076674645527233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49515106092102232860702977 37136329569076674645527233)
              ·
                refine ⟨27852247176807505984145425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37136329569076674645527233 27852247176807505984145425)
                ·
                  refine ⟨20889185382605629488109069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27852247176807505984145425 20889185382605629488109069)
                  ·
                    refine ⟨7833444518477111058040901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20889185382605629488109069 7833444518477111058040901)
                    ·
                      refine ⟨1468770847214458323382669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7833444518477111058040901 1468770847214458323382669)
                      ·
                        rfl

theorem cell23_2860421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 3, 4].length) (baseStart_2860421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2860421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2860421 prefixEnd_2860421 := by exact prefixLift 2860421
  have htrace : WordTrace (prefixWord ++ tailWord_2860421) baseStart_2860421 baseEnd_2860421 := by
    simpa [prefixWord, tailWord_2860421, baseEnd_2860421] using wordTrace_append hprefix tailTrace_2860421
  have hstable : (prefixWord ++ tailWord_2860421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2860421).length < 2 ^ (prefixWord ++ tailWord_2860421).sum := by decide
  have hdescent : baseEnd_2860421 < baseStart_2860421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2860421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2860441 : List Nat := [1, 2, 1, 2, 1, 5, 1, 1, 1, 3, 5]
def baseStart_2860441 : Nat := 118140960795 + 2860441 * 2 ^ 59
def prefixEnd_2860441 : Nat := 4983230072969 + 3 ^ 40 * 2860441 * 2
def baseEnd_2860441 : Nat := 1468781116827548245132577

theorem tailTrace_2860441 : CollatzResearch.WordTrace tailWord_2860441 prefixEnd_2860441 1468781116827548245132577 := by
  unfold tailWord_2860441
  simp only [CollatzResearch.WordTrace]
  refine ⟨104328854230118256274493177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69552569486745504182995451 104328854230118256274493177)
  ·
    refine ⟨78246640672588692205869883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104328854230118256274493177 78246640672588692205869883)
    ·
      refine ⟨117369961008883038308804825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78246640672588692205869883 117369961008883038308804825)
      ·
        refine ⟨88027470756662278731603619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117369961008883038308804825 88027470756662278731603619)
        ·
          refine ⟨132041206134993418097405429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88027470756662278731603619 132041206134993418097405429)
          ·
            refine ⟨12378863075155632946631759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 132041206134993418097405429 12378863075155632946631759)
            ·
              refine ⟨18568294612733449419947639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12378863075155632946631759 18568294612733449419947639)
              ·
                refine ⟨27852441919100174129921459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18568294612733449419947639 27852441919100174129921459)
                ·
                  refine ⟨41778662878650261194882189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27852441919100174129921459 41778662878650261194882189)
                  ·
                    refine ⟨15666998579493847948080821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41778662878650261194882189 15666998579493847948080821)
                    ·
                      refine ⟨1468781116827548245132577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15666998579493847948080821 1468781116827548245132577)
                      ·
                        rfl

theorem cell23_2860441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 3, 5].length) (baseStart_2860441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2860441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2860441 prefixEnd_2860441 := by exact prefixLift 2860441
  have htrace : WordTrace (prefixWord ++ tailWord_2860441) baseStart_2860441 baseEnd_2860441 := by
    simpa [prefixWord, tailWord_2860441, baseEnd_2860441] using wordTrace_append hprefix tailTrace_2860441
  have hstable : (prefixWord ++ tailWord_2860441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2860441).length < 2 ^ (prefixWord ++ tailWord_2860441).sum := by decide
  have hdescent : baseEnd_2860441 < baseStart_2860441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2860441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2860476 : List Nat := [2, 2, 2, 4, 3, 1, 1, 2, 1, 3, 2]
def baseStart_2860476 : Nat := 118140960795 + 2860476 * 2 ^ 59
def prefixEnd_2860476 : Nat := 4983230072969 + 3 ^ 40 * 2860476 * 2
def baseEnd_2860476 : Nat := 1468799088650455608194917

theorem tailTrace_2860476 : CollatzResearch.WordTrace tailWord_2860476 prefixEnd_2860476 1468799088650455608194917 := by
  unfold tailWord_2860476
  simp only [CollatzResearch.WordTrace]
  refine ⟨52165065392495728626008641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69553420523327638168011521 52165065392495728626008641)
  ·
    refine ⟨39123799044371796469506481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52165065392495728626008641 39123799044371796469506481)
    ·
      refine ⟨29342849283278847352129861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39123799044371796469506481 29342849283278847352129861)
      ·
        refine ⟨5501784240614783878524349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29342849283278847352129861 5501784240614783878524349)
        ·
          refine ⟨2063169090230543954446631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5501784240614783878524349 2063169090230543954446631)
          ·
            refine ⟨3094753635345815931669947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2063169090230543954446631 3094753635345815931669947)
            ·
              refine ⟨4642130453018723897504921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3094753635345815931669947 4642130453018723897504921)
              ·
                refine ⟨3481597839764042923128691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4642130453018723897504921 3481597839764042923128691)
                ·
                  refine ⟨5222396759646064384693037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3481597839764042923128691 5222396759646064384693037)
                  ·
                    refine ⟨1958398784867274144259889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5222396759646064384693037 1958398784867274144259889)
                    ·
                      refine ⟨1468799088650455608194917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1958398784867274144259889 1468799088650455608194917)
                      ·
                        rfl

theorem cell23_2860476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_2860476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2860476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2860476 prefixEnd_2860476 := by exact prefixLift 2860476
  have htrace : WordTrace (prefixWord ++ tailWord_2860476) baseStart_2860476 baseEnd_2860476 := by
    simpa [prefixWord, tailWord_2860476, baseEnd_2860476] using wordTrace_append hprefix tailTrace_2860476
  have hstable : (prefixWord ++ tailWord_2860476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2860476).length < 2 ^ (prefixWord ++ tailWord_2860476).sum := by decide
  have hdescent : baseEnd_2860476 < baseStart_2860476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2860476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2860491 : List Nat := [1, 1, 1, 1, 3, 3, 2, 3, 1, 7]
def baseStart_2860491 : Nat := 118140960795 + 2860491 * 2 ^ 59
def prefixEnd_2860491 : Nat := 4983230072969 + 3 ^ 40 * 2860491 * 2
def baseEnd_2860491 : Nat := 489602263620091016502449

theorem tailTrace_2860491 : CollatzResearch.WordTrace tailWord_2860491 prefixEnd_2860491 489602263620091016502449 := by
  unfold tailWord_2860491
  simp only [CollatzResearch.WordTrace]
  refine ⟨104330677879937114813813327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69553785253291409875875551 104330677879937114813813327)
  ·
    refine ⟨156496016819905672220719991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104330677879937114813813327 156496016819905672220719991)
    ·
      refine ⟨234744025229858508331079987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156496016819905672220719991 234744025229858508331079987)
      ·
        refine ⟨352116037844787762496619981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234744025229858508331079987 352116037844787762496619981)
        ·
          refine ⟨132043514191795410936232493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 352116037844787762496619981 132043514191795410936232493)
          ·
            refine ⟨49516317821923279101087185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132043514191795410936232493 49516317821923279101087185)
            ·
              refine ⟨37137238366442459325815389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49516317821923279101087185 37137238366442459325815389)
              ·
                refine ⟨13926464387415922247180771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37137238366442459325815389 13926464387415922247180771)
                ·
                  refine ⟨20889696581123883370771157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13926464387415922247180771 20889696581123883370771157)
                  ·
                    refine ⟨489602263620091016502449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20889696581123883370771157 489602263620091016502449)
                    ·
                      rfl

theorem cell23_2860491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 7].length) (baseStart_2860491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2860491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2860491 prefixEnd_2860491 := by exact prefixLift 2860491
  have htrace : WordTrace (prefixWord ++ tailWord_2860491) baseStart_2860491 baseEnd_2860491 := by
    simpa [prefixWord, tailWord_2860491, baseEnd_2860491] using wordTrace_append hprefix tailTrace_2860491
  have hstable : (prefixWord ++ tailWord_2860491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2860491).length < 2 ^ (prefixWord ++ tailWord_2860491).sum := by decide
  have hdescent : baseEnd_2860491 < baseStart_2860491 := by decide
  rcases family_descends (prefixWord ++ tailWord_2860491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2860515 : List Nat := [1, 1, 1, 6, 2, 1, 1, 1, 2, 5, 2]
def baseStart_2860515 : Nat := 118140960795 + 2860515 * 2 ^ 59
def prefixEnd_2860515 : Nat := 4983230072969 + 3 ^ 40 * 2860515 * 2
def baseEnd_2860515 : Nat := 1468819114395980955607237

theorem tailTrace_2860515 : CollatzResearch.WordTrace tailWord_2860515 prefixEnd_2860515 1468819114395980955607237 := by
  unfold tailWord_2860515
  simp only [CollatzResearch.WordTrace]
  refine ⟨104331553231850166912686999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69554368821233444608457999 104331553231850166912686999)
  ·
    refine ⟨156497329847775250369030499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104331553231850166912686999 156497329847775250369030499)
    ·
      refine ⟨234745994771662875553545749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156497329847775250369030499 234745994771662875553545749)
      ·
        refine ⟨11003718504921697291572457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 234745994771662875553545749 11003718504921697291572457)
        ·
          refine ⟨8252788878691272968679343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11003718504921697291572457 8252788878691272968679343)
          ·
            refine ⟨12379183318036909453019015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8252788878691272968679343 12379183318036909453019015)
            ·
              refine ⟨18568774977055364179528523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12379183318036909453019015 18568774977055364179528523)
              ·
                refine ⟨27853162465583046269292785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18568774977055364179528523 27853162465583046269292785)
                ·
                  refine ⟨20889871849187284701969589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27853162465583046269292785 20889871849187284701969589)
                  ·
                    refine ⟨1958425485861307940809649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20889871849187284701969589 1958425485861307940809649)
                    ·
                      refine ⟨1468819114395980955607237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1958425485861307940809649 1468819114395980955607237)
                      ·
                        rfl

theorem cell23_2860515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 5, 2].length) (baseStart_2860515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2860515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2860515 prefixEnd_2860515 := by exact prefixLift 2860515
  have htrace : WordTrace (prefixWord ++ tailWord_2860515) baseStart_2860515 baseEnd_2860515 := by
    simpa [prefixWord, tailWord_2860515, baseEnd_2860515] using wordTrace_append hprefix tailTrace_2860515
  have hstable : (prefixWord ++ tailWord_2860515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2860515).length < 2 ^ (prefixWord ++ tailWord_2860515).sum := by decide
  have hdescent : baseEnd_2860515 < baseStart_2860515 := by decide
  rcases family_descends (prefixWord ++ tailWord_2860515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2860542 : List Nat := [4, 2, 2, 3, 1, 1, 1, 1, 1, 7]
def baseStart_2860542 : Nat := 118140960795 + 2860542 * 2 ^ 59
def prefixEnd_2860542 : Nat := 4983230072969 + 3 ^ 40 * 2860542 * 2
def baseEnd_2860542 : Nat := 489610992791217449989871

theorem tailTrace_2860542 : CollatzResearch.WordTrace tailWord_2860542 prefixEnd_2860542 489610992791217449989871 := by
  unfold tailWord_2860542
  simp only [CollatzResearch.WordTrace]
  refine ⟨13041567250344043815489985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69555025335168233682613253 13041567250344043815489985)
  ·
    refine ⟨9781175437758032861617489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13041567250344043815489985 9781175437758032861617489)
    ·
      refine ⟨7335881578318524646213117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9781175437758032861617489 7335881578318524646213117)
      ·
        refine ⟨2750955591869446742329919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7335881578318524646213117 2750955591869446742329919)
        ·
          refine ⟨4126433387804170113494879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2750955591869446742329919 4126433387804170113494879)
          ·
            refine ⟨6189650081706255170242319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4126433387804170113494879 6189650081706255170242319)
            ·
              refine ⟨9284475122559382755363479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6189650081706255170242319 9284475122559382755363479)
              ·
                refine ⟨13926712683839074133045219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9284475122559382755363479 13926712683839074133045219)
                ·
                  refine ⟨20890069025758611199567829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13926712683839074133045219 20890069025758611199567829)
                  ·
                    refine ⟨489610992791217449989871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20890069025758611199567829 489610992791217449989871)
                    ·
                      rfl

theorem cell23_2860542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_2860542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2860542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2860542 prefixEnd_2860542 := by exact prefixLift 2860542
  have htrace : WordTrace (prefixWord ++ tailWord_2860542) baseStart_2860542 baseEnd_2860542 := by
    simpa [prefixWord, tailWord_2860542, baseEnd_2860542] using wordTrace_append hprefix tailTrace_2860542
  have hstable : (prefixWord ++ tailWord_2860542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2860542).length < 2 ^ (prefixWord ++ tailWord_2860542).sum := by decide
  have hdescent : baseEnd_2860542 < baseStart_2860542 := by decide
  rcases family_descends (prefixWord ++ tailWord_2860542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2860545 : List Nat := [1, 2, 4, 1, 4, 1, 1, 1, 1, 3, 4]
def baseStart_2860545 : Nat := 118140960795 + 2860545 * 2 ^ 59
def prefixEnd_2860545 : Nat := 4983230072969 + 3 ^ 40 * 2860545 * 2
def baseEnd_2860545 : Nat := 1468834518815615838232099

theorem tailTrace_2860545 : CollatzResearch.WordTrace tailWord_2860545 prefixEnd_2860545 1468834518815615838232099 := by
  unfold tailWord_2860545
  simp only [CollatzResearch.WordTrace]
  refine ⟨104332647421741482036279089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69555098281160988024186059 104332647421741482036279089)
  ·
    refine ⟨78249485566306111527209317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104332647421741482036279089 78249485566306111527209317)
    ·
      refine ⟨14671778543682395911351747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78249485566306111527209317 14671778543682395911351747)
      ·
        refine ⟨22007667815523593867027621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14671778543682395911351747 22007667815523593867027621)
        ·
          refine ⟨4126437715410673850067679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22007667815523593867027621 4126437715410673850067679)
          ·
            refine ⟨6189656573116010775101519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4126437715410673850067679 6189656573116010775101519)
            ·
              refine ⟨9284484859674016162652279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6189656573116010775101519 9284484859674016162652279)
              ·
                refine ⟨13926727289511024243978419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9284484859674016162652279 13926727289511024243978419)
                ·
                  refine ⟨20890090934266536365967629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13926727289511024243978419 20890090934266536365967629)
                  ·
                    refine ⟨7833784100349951137237861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20890090934266536365967629 7833784100349951137237861)
                    ·
                      refine ⟨1468834518815615838232099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7833784100349951137237861 1468834518815615838232099)
                      ·
                        rfl

theorem cell23_2860545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 3, 4].length) (baseStart_2860545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2860545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2860545 prefixEnd_2860545 := by exact prefixLift 2860545
  have htrace : WordTrace (prefixWord ++ tailWord_2860545) baseStart_2860545 baseEnd_2860545 := by
    simpa [prefixWord, tailWord_2860545, baseEnd_2860545] using wordTrace_append hprefix tailTrace_2860545
  have hstable : (prefixWord ++ tailWord_2860545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2860545).length < 2 ^ (prefixWord ++ tailWord_2860545).sum := by decide
  have hdescent : baseEnd_2860545 < baseStart_2860545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2860545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2860572 : List Nat := [2, 2, 3, 1, 2, 1, 1, 6, 1, 4]
def baseStart_2860572 : Nat := 118140960795 + 2860572 * 2 ^ 59
def prefixEnd_2860572 : Nat := 4983230072969 + 3 ^ 40 * 2860572 * 2
def baseEnd_2860572 : Nat := 489616127597762410864825

theorem tailTrace_2860572 : CollatzResearch.WordTrace tailWord_2860572 prefixEnd_2860572 489616127597762410864825 := by
  unfold tailWord_2860572
  simp only [CollatzResearch.WordTrace]
  refine ⟨52166816096321832823755985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69555754795095777098341313 52166816096321832823755985)
  ·
    refine ⟨39125112072241374617816989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52166816096321832823755985 39125112072241374617816989)
    ·
      refine ⟨14671917027090515481681371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39125112072241374617816989 14671917027090515481681371)
      ·
        refine ⟨22007875540635773222522057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14671917027090515481681371 22007875540635773222522057)
        ·
          refine ⟨16505906655476829916891543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22007875540635773222522057 16505906655476829916891543)
          ·
            refine ⟨24758859983215244875337315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16505906655476829916891543 24758859983215244875337315)
            ·
              refine ⟨37138289974822867313005973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24758859983215244875337315 37138289974822867313005973)
              ·
                refine ⟨1740857342569821905297155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 37138289974822867313005973 1740857342569821905297155)
                ·
                  refine ⟨2611286013854732857945733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1740857342569821905297155 2611286013854732857945733)
                  ·
                    refine ⟨489616127597762410864825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2611286013854732857945733 489616127597762410864825)
                    ·
                      rfl

theorem cell23_2860572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 6, 1, 4].length) (baseStart_2860572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2860572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2860572 prefixEnd_2860572 := by exact prefixLift 2860572
  have htrace : WordTrace (prefixWord ++ tailWord_2860572) baseStart_2860572 baseEnd_2860572 := by
    simpa [prefixWord, tailWord_2860572, baseEnd_2860572] using wordTrace_append hprefix tailTrace_2860572
  have hstable : (prefixWord ++ tailWord_2860572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2860572).length < 2 ^ (prefixWord ++ tailWord_2860572).sum := by decide
  have hdescent : baseEnd_2860572 < baseStart_2860572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2860572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2860652 : List Nat := [2, 2, 1, 1, 3, 1, 1, 3, 5, 2, 2]
def baseStart_2860652 : Nat := 118140960795 + 2860652 * 2 ^ 59
def prefixEnd_2860652 : Nat := 4983230072969 + 3 ^ 40 * 2860652 * 2
def baseEnd_2860652 : Nat := 1468889461245646919594107

theorem tailTrace_2860652 : CollatzResearch.WordTrace tailWord_2860652 prefixEnd_2860652 1468889461245646919594107 := by
  unfold tailWord_2860652
  simp only [CollatzResearch.WordTrace]
  refine ⟨52168275016176919655212105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69557700021569226206949473 52168275016176919655212105)
  ·
    refine ⟨39126206262132689741409079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52168275016176919655212105 39126206262132689741409079)
    ·
      refine ⟨58689309393199034612113619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39126206262132689741409079 58689309393199034612113619)
      ·
        refine ⟨88033964089798551918170429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58689309393199034612113619 88033964089798551918170429)
        ·
          refine ⟨33012736533674456969313911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88033964089798551918170429 33012736533674456969313911)
          ·
            refine ⟨49519104800511685453970867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33012736533674456969313911 49519104800511685453970867)
            ·
              refine ⟨74278657200767528180956301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49519104800511685453970867 74278657200767528180956301)
              ·
                refine ⟨27854496450287823067858613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74278657200767528180956301 27854496450287823067858613)
                ·
                  refine ⟨2611359042214483412611745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27854496450287823067858613 2611359042214483412611745)
                  ·
                    refine ⟨1958519281660862559458809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2611359042214483412611745 1958519281660862559458809)
                    ·
                      refine ⟨1468889461245646919594107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1958519281660862559458809 1468889461245646919594107)
                      ·
                        rfl

theorem cell23_2860652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 2, 2].length) (baseStart_2860652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2860652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2860652 prefixEnd_2860652 := by exact prefixLift 2860652
  have htrace : WordTrace (prefixWord ++ tailWord_2860652) baseStart_2860652 baseEnd_2860652 := by
    simpa [prefixWord, tailWord_2860652, baseEnd_2860652] using wordTrace_append hprefix tailTrace_2860652
  have hstable : (prefixWord ++ tailWord_2860652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2860652).length < 2 ^ (prefixWord ++ tailWord_2860652).sum := by decide
  have hdescent : baseEnd_2860652 < baseStart_2860652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2860652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2860662 : List Nat := [5, 1, 1, 2, 2, 2, 1, 2, 1, 6]
def baseStart_2860662 : Nat := 118140960795 + 2860662 * 2 ^ 59
def prefixEnd_2860662 : Nat := 4983230072969 + 3 ^ 40 * 2860662 * 2
def baseEnd_2860662 : Nat := 489631532017397293489687

theorem tailTrace_2860662 : CollatzResearch.WordTrace tailWord_2860662 prefixEnd_2860662 489631532017397293489687 := by
  unfold tailWord_2860662
  simp only [CollatzResearch.WordTrace]
  refine ⟨6521057172644850688643015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69557943174878407345525493 6521057172644850688643015)
  ·
    refine ⟨9781585758967276032964523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6521057172644850688643015 9781585758967276032964523)
    ·
      refine ⟨14672378638450914049446785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9781585758967276032964523 14672378638450914049446785)
      ·
        refine ⟨11004283978838185537085089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14672378638450914049446785 11004283978838185537085089)
        ·
          refine ⟨8253212984128639152813817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11004283978838185537085089 8253212984128639152813817)
          ·
            refine ⟨6189909738096479364610363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8253212984128639152813817 6189909738096479364610363)
            ·
              refine ⟨9284864607144719046915545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6189909738096479364610363 9284864607144719046915545)
              ·
                refine ⟨6963648455358539285186659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9284864607144719046915545 6963648455358539285186659)
                ·
                  refine ⟨10445472683037808927779989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6963648455358539285186659 10445472683037808927779989)
                  ·
                    refine ⟨489631532017397293489687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10445472683037808927779989 489631532017397293489687)
                    ·
                      rfl

theorem cell23_2860662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 2, 1, 6].length) (baseStart_2860662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2860662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2860662 prefixEnd_2860662 := by exact prefixLift 2860662
  have htrace : WordTrace (prefixWord ++ tailWord_2860662) baseStart_2860662 baseEnd_2860662 := by
    simpa [prefixWord, tailWord_2860662, baseEnd_2860662] using wordTrace_append hprefix tailTrace_2860662
  have hstable : (prefixWord ++ tailWord_2860662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2860662).length < 2 ^ (prefixWord ++ tailWord_2860662).sum := by decide
  have hdescent : baseEnd_2860662 < baseStart_2860662 := by decide
  rcases family_descends (prefixWord ++ tailWord_2860662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2860665 : List Nat := [1, 2, 1, 3, 3, 1, 3, 2, 1, 2, 4]
def baseStart_2860665 : Nat := 118140960795 + 2860665 * 2 ^ 59
def prefixEnd_2860665 : Nat := 4983230072969 + 3 ^ 40 * 2860665 * 2
def baseEnd_2860665 : Nat := 1468896136494155368731547

theorem tailTrace_2860665 : CollatzResearch.WordTrace tailWord_2860665 prefixEnd_2860665 1468896136494155368731547 := by
  unfold tailWord_2860665
  simp only [CollatzResearch.WordTrace]
  refine ⟨104337024181306742530647449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69558016120871161687098299 104337024181306742530647449)
  ·
    refine ⟨78252768135980056897985587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104337024181306742530647449 78252768135980056897985587)
    ·
      refine ⟨117379152203970085346978381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78252768135980056897985587 117379152203970085346978381)
      ·
        refine ⟨44017182076488782005116893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117379152203970085346978381 44017182076488782005116893)
        ·
          refine ⟨16506443278683293251918835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44017182076488782005116893 16506443278683293251918835)
          ·
            refine ⟨24759664918024939877878253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16506443278683293251918835 24759664918024939877878253)
            ·
              refine ⟨9284874344259352454204345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24759664918024939877878253 9284874344259352454204345)
              ·
                refine ⟨6963655758194514340653259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9284874344259352454204345 6963655758194514340653259)
                ·
                  refine ⟨10445483637291771510979889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6963655758194514340653259 10445483637291771510979889)
                  ·
                    refine ⟨7834112727968828633234917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10445483637291771510979889 7834112727968828633234917)
                    ·
                      refine ⟨1468896136494155368731547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7834112727968828633234917 1468896136494155368731547)
                      ·
                        rfl

theorem cell23_2860665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 2, 1, 2, 4].length) (baseStart_2860665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2860665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2860665 prefixEnd_2860665 := by exact prefixLift 2860665
  have htrace : WordTrace (prefixWord ++ tailWord_2860665) baseStart_2860665 baseEnd_2860665 := by
    simpa [prefixWord, tailWord_2860665, baseEnd_2860665] using wordTrace_append hprefix tailTrace_2860665
  have hstable : (prefixWord ++ tailWord_2860665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2860665).length < 2 ^ (prefixWord ++ tailWord_2860665).sum := by decide
  have hdescent : baseEnd_2860665 < baseStart_2860665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2860665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2860669 : List Nat := [1, 4, 1, 1, 4, 2, 3, 1, 1, 1, 4]
def baseStart_2860669 : Nat := 118140960795 + 2860669 * 2 ^ 59
def prefixEnd_2860669 : Nat := 4983230072969 + 3 ^ 40 * 2860669 * 2
def baseEnd_2860669 : Nat := 1468898190416773353081529

theorem tailTrace_2860669 : CollatzResearch.WordTrace tailWord_2860669 prefixEnd_2860669 1468898190416773353081529 := by
  unfold tailWord_2860669
  simp only [CollatzResearch.WordTrace]
  refine ⟨104337170073292251213793061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69558113382194834142528707 104337170073292251213793061)
  ·
    refine ⟨19563219388742297102586199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104337170073292251213793061 19563219388742297102586199)
    ·
      refine ⟨29344829083113445653879299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19563219388742297102586199 29344829083113445653879299)
      ·
        refine ⟨44017243624670168480818949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29344829083113445653879299 44017243624670168480818949)
        ·
          refine ⟨8253233179625656590153553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44017243624670168480818949 8253233179625656590153553)
          ·
            refine ⟨6189924884719242442615165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8253233179625656590153553 6189924884719242442615165)
            ·
              refine ⟨2321221831769715915980687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6189924884719242442615165 2321221831769715915980687)
              ·
                refine ⟨3481832747654573873971031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2321221831769715915980687 3481832747654573873971031)
                ·
                  refine ⟨5222749121481860810956547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3481832747654573873971031 5222749121481860810956547)
                  ·
                    refine ⟨7834123682222791216434821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5222749121481860810956547 7834123682222791216434821)
                    ·
                      refine ⟨1468898190416773353081529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7834123682222791216434821 1468898190416773353081529)
                      ·
                        rfl

theorem cell23_2860669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 3, 1, 1, 1, 4].length) (baseStart_2860669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2860669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2860669 prefixEnd_2860669 := by exact prefixLift 2860669
  have htrace : WordTrace (prefixWord ++ tailWord_2860669) baseStart_2860669 baseEnd_2860669 := by
    simpa [prefixWord, tailWord_2860669, baseEnd_2860669] using wordTrace_append hprefix tailTrace_2860669
  have hstable : (prefixWord ++ tailWord_2860669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2860669).length < 2 ^ (prefixWord ++ tailWord_2860669).sum := by decide
  have hdescent : baseEnd_2860669 < baseStart_2860669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2860669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2860680 : List Nat := [2, 1, 3, 5, 1, 2, 2, 2, 1, 1, 3]
def baseStart_2860680 : Nat := 118140960795 + 2860680 * 2 ^ 59
def prefixEnd_2860680 : Nat := 4983230072969 + 3 ^ 40 * 2860680 * 2
def baseEnd_2860680 : Nat := 1468903838703972810043979

theorem tailTrace_2860680 : CollatzResearch.WordTrace tailWord_2860680 prefixEnd_2860680 1468903838703972810043979 := by
  unfold tailWord_2860680
  simp only [CollatzResearch.WordTrace]
  refine ⟨52168785638126200046221747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69558380850834933394962329 52168785638126200046221747)
  ·
    refine ⟨78253178457189300069332621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52168785638126200046221747 78253178457189300069332621)
    ·
      refine ⟨29344941921445987525999733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78253178457189300069332621 29344941921445987525999733)
      ·
        refine ⟨2751088305135561330562475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29344941921445987525999733 2751088305135561330562475)
        ·
          refine ⟨4126632457703341995843713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2751088305135561330562475 4126632457703341995843713)
          ·
            refine ⟨3094974343277506496882785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4126632457703341995843713 3094974343277506496882785)
            ·
              refine ⟨2321230757458129872662089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3094974343277506496882785 2321230757458129872662089)
              ·
                refine ⟨1740923068093597404496567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2321230757458129872662089 1740923068093597404496567)
                ·
                  refine ⟨2611384602140396106744851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1740923068093597404496567 2611384602140396106744851)
                  ·
                    refine ⟨3917076903210594160117277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2611384602140396106744851 3917076903210594160117277)
                    ·
                      refine ⟨1468903838703972810043979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3917076903210594160117277 1468903838703972810043979)
                      ·
                        rfl

theorem cell23_2860680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_2860680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2860680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2860680 prefixEnd_2860680 := by exact prefixLift 2860680
  have htrace : WordTrace (prefixWord ++ tailWord_2860680) baseStart_2860680 baseEnd_2860680 := by
    simpa [prefixWord, tailWord_2860680, baseEnd_2860680] using wordTrace_append hprefix tailTrace_2860680
  have hstable : (prefixWord ++ tailWord_2860680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2860680).length < 2 ^ (prefixWord ++ tailWord_2860680).sum := by decide
  have hdescent : baseEnd_2860680 < baseStart_2860680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2860680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2860815 : List Nat := [1, 1, 2, 1, 1, 1, 4, 4, 1, 3, 4]
def baseStart_2860815 : Nat := 118140960795 + 2860815 * 2 ^ 59
def prefixEnd_2860815 : Nat := 4983230072969 + 3 ^ 40 * 2860815 * 2
def baseEnd_2860815 : Nat := 1468973158592329781855857

theorem tailTrace_2860815 : CollatzResearch.WordTrace tailWord_2860815 prefixEnd_2860815 1468973158592329781855857 := by
  unfold tailWord_2860815
  simp only [CollatzResearch.WordTrace]
  refine ⟨104342495130763318148607899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69561663420508878765738599 104342495130763318148607899)
  ·
    refine ⟨156513742696144977222911849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104342495130763318148607899 156513742696144977222911849)
    ·
      refine ⟨117385307022108732917183887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156513742696144977222911849 117385307022108732917183887)
      ·
        refine ⟨176077960533163099375775831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117385307022108732917183887 176077960533163099375775831)
        ·
          refine ⟨264116940799744649063663747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176077960533163099375775831 264116940799744649063663747)
          ·
            refine ⟨396175411199616973595495621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264116940799744649063663747 396175411199616973595495621)
            ·
              refine ⟨74282889599928182549155429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 396175411199616973595495621 74282889599928182549155429)
              ·
                refine ⟨13928041799986534227966643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74282889599928182549155429 13928041799986534227966643)
                ·
                  refine ⟨20892062699979801341949965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13928041799986534227966643 20892062699979801341949965)
                  ·
                    refine ⟨7834523512492425503231237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20892062699979801341949965 7834523512492425503231237)
                    ·
                      refine ⟨1468973158592329781855857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7834523512492425503231237 1468973158592329781855857)
                      ·
                        rfl

theorem cell23_2860815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 3, 4].length) (baseStart_2860815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2860815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2860815 prefixEnd_2860815 := by exact prefixLift 2860815
  have htrace : WordTrace (prefixWord ++ tailWord_2860815) baseStart_2860815 baseEnd_2860815 := by
    simpa [prefixWord, tailWord_2860815, baseEnd_2860815] using wordTrace_append hprefix tailTrace_2860815
  have hstable : (prefixWord ++ tailWord_2860815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2860815).length < 2 ^ (prefixWord ++ tailWord_2860815).sum := by decide
  have hdescent : baseEnd_2860815 < baseStart_2860815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2860815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2860872 : List Nat := [2, 1, 3, 1, 1, 4, 2, 3, 6]
def baseStart_2860872 : Nat := 118140960795 + 2860872 * 2 ^ 59
def prefixEnd_2860872 : Nat := 4983230072969 + 3 ^ 40 * 2860872 * 2
def baseEnd_2860872 : Nat := 163222491887737339871455

theorem tailTrace_2860872 : CollatzResearch.WordTrace tailWord_2860872 prefixEnd_2860872 163222491887737339871455 := by
  unfold tailWord_2860872
  simp only [CollatzResearch.WordTrace]
  refine ⟨52172287045778408441716435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69563049394371211255621913 52172287045778408441716435)
  ·
    refine ⟨78258430568667612662574653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52172287045778408441716435 78258430568667612662574653)
    ·
      refine ⟨29346911463250354748465495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78258430568667612662574653 29346911463250354748465495)
      ·
        refine ⟨44020367194875532122698243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29346911463250354748465495 44020367194875532122698243)
        ·
          refine ⟨66030550792313298184047365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44020367194875532122698243 66030550792313298184047365)
          ·
            refine ⟨12380728273558743409508881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66030550792313298184047365 12380728273558743409508881)
            ·
              refine ⟨9285546205169057557131661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12380728273558743409508881 9285546205169057557131661)
              ·
                refine ⟨3482079826938396583924373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9285546205169057557131661 3482079826938396583924373)
                ·
                  refine ⟨163222491887737339871455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3482079826938396583924373 163222491887737339871455)
                  ·
                    rfl

theorem cell23_2860872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 3, 6].length) (baseStart_2860872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2860872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2860872 prefixEnd_2860872 := by exact prefixLift 2860872
  have htrace : WordTrace (prefixWord ++ tailWord_2860872) baseStart_2860872 baseEnd_2860872 := by
    simpa [prefixWord, tailWord_2860872, baseEnd_2860872] using wordTrace_append hprefix tailTrace_2860872
  have hstable : (prefixWord ++ tailWord_2860872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2860872).length < 2 ^ (prefixWord ++ tailWord_2860872).sum := by decide
  have hdescent : baseEnd_2860872 < baseStart_2860872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2860872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2860922 : List Nat := [3, 1, 1, 1, 1, 1, 4, 1, 5, 1, 4]
def baseStart_2860922 : Nat := 118140960795 + 2860922 * 2 ^ 59
def prefixEnd_2860922 : Nat := 4983230072969 + 3 ^ 40 * 2860922 * 2
def baseEnd_2860922 : Nat := 1469028101022360863217865

theorem tailTrace_2860922 : CollatzResearch.WordTrace tailWord_2860922 prefixEnd_2860922 1469028101022360863217865 := by
  unfold tailWord_2860922
  simp only [CollatzResearch.WordTrace]
  refine ⟨26086599435343918855688255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69564265160917116948502013 26086599435343918855688255)
  ·
    refine ⟨39129899153015878283532383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26086599435343918855688255 39129899153015878283532383)
    ·
      refine ⟨58694848729523817425298575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39129899153015878283532383 58694848729523817425298575)
      ·
        refine ⟨88042273094285726137947863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58694848729523817425298575 88042273094285726137947863)
        ·
          refine ⟨132063409641428589206921795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88042273094285726137947863 132063409641428589206921795)
          ·
            refine ⟨198095114462142883810382693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132063409641428589206921795 198095114462142883810382693)
            ·
              refine ⟨37142833961651790714446755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 198095114462142883810382693 37142833961651790714446755)
              ·
                refine ⟨55714250942477686071670133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37142833961651790714446755 55714250942477686071670133)
                ·
                  refine ⟨5223211025857283069219075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55714250942477686071670133 5223211025857283069219075)
                  ·
                    refine ⟨7834816538785924603828613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5223211025857283069219075 7834816538785924603828613)
                    ·
                      refine ⟨1469028101022360863217865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7834816538785924603828613 1469028101022360863217865)
                      ·
                        rfl

theorem cell23_2860922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 5, 1, 4].length) (baseStart_2860922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2860922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2860922 prefixEnd_2860922 := by exact prefixLift 2860922
  have htrace : WordTrace (prefixWord ++ tailWord_2860922) baseStart_2860922 baseEnd_2860922 := by
    simpa [prefixWord, tailWord_2860922, baseEnd_2860922] using wordTrace_append hprefix tailTrace_2860922
  have hstable : (prefixWord ++ tailWord_2860922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2860922).length < 2 ^ (prefixWord ++ tailWord_2860922).sum := by decide
  have hdescent : baseEnd_2860922 < baseStart_2860922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2860922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2860936 : List Nat := [2, 1, 3, 3, 3, 1, 2, 2, 1, 5]
def baseStart_2860936 : Nat := 118140960795 + 2860936 * 2 ^ 59
def prefixEnd_2860936 : Nat := 4983230072969 + 3 ^ 40 * 2860936 * 2
def baseEnd_2860936 : Nat := 489678429917174602814267

theorem tailTrace_2860936 : CollatzResearch.WordTrace tailWord_2860936 prefixEnd_2860936 489678429917174602814267 := by
  unfold tailWord_2860936
  simp only [CollatzResearch.WordTrace]
  refine ⟨52173454181662477906881331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69564605575549970542508441 52173454181662477906881331)
  ·
    refine ⟨78260181272493716860321997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52173454181662477906881331 78260181272493716860321997)
    ·
      refine ⟨29347567977185143822620749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78260181272493716860321997 29347567977185143822620749)
      ·
        refine ⟨11005337991444428933482781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29347567977185143822620749 11005337991444428933482781)
        ·
          refine ⟨4127001746791660850056043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11005337991444428933482781 4127001746791660850056043)
          ·
            refine ⟨6190502620187491275084065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4127001746791660850056043 6190502620187491275084065)
            ·
              refine ⟨4642876965140618456313049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6190502620187491275084065 4642876965140618456313049)
              ·
                refine ⟨3482157723855463842234787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4642876965140618456313049 3482157723855463842234787)
                ·
                  refine ⟨5223236585783195763352181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3482157723855463842234787 5223236585783195763352181)
                  ·
                    refine ⟨489678429917174602814267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5223236585783195763352181 489678429917174602814267)
                    ·
                      rfl

theorem cell23_2860936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 2, 1, 5].length) (baseStart_2860936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2860936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2860936 prefixEnd_2860936 := by exact prefixLift 2860936
  have htrace : WordTrace (prefixWord ++ tailWord_2860936) baseStart_2860936 baseEnd_2860936 := by
    simpa [prefixWord, tailWord_2860936, baseEnd_2860936] using wordTrace_append hprefix tailTrace_2860936
  have hstable : (prefixWord ++ tailWord_2860936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2860936).length < 2 ^ (prefixWord ++ tailWord_2860936).sum := by decide
  have hdescent : baseEnd_2860936 < baseStart_2860936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2860936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2860956 : List Nat := [2, 2, 3, 3, 1, 1, 2, 3, 1, 1, 4]
def baseStart_2860956 : Nat := 118140960795 + 2860956 * 2 ^ 59
def prefixEnd_2860956 : Nat := 4983230072969 + 3 ^ 40 * 2860956 * 2
def baseEnd_2860956 : Nat := 1469045559364613730192709

theorem tailTrace_2860956 : CollatzResearch.WordTrace tailWord_2860956 prefixEnd_2860956 1469045559364613730192709 := by
  unfold tailWord_2860956
  simp only [CollatzResearch.WordTrace]
  refine ⟨52173818911626249614745361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69565091882168332819660481 52173818911626249614745361)
  ·
    refine ⟨39130364183719687211059021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52173818911626249614745361 39130364183719687211059021)
    ·
      refine ⟨14673886568894882704147133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39130364183719687211059021 14673886568894882704147133)
      ·
        refine ⟨5502707463335581014055175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14673886568894882704147133 5502707463335581014055175)
        ·
          refine ⟨8254061195003371521082763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5502707463335581014055175 8254061195003371521082763)
          ·
            refine ⟨12381091792505057281624145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8254061195003371521082763 12381091792505057281624145)
            ·
              refine ⟨9285818844378792961218109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12381091792505057281624145 9285818844378792961218109)
              ·
                refine ⟨3482182066642047360456791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9285818844378792961218109 3482182066642047360456791)
                ·
                  refine ⟨5223273099963071040685187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3482182066642047360456791 5223273099963071040685187)
                  ·
                    refine ⟨7834909649944606561027781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5223273099963071040685187 7834909649944606561027781)
                    ·
                      refine ⟨1469045559364613730192709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7834909649944606561027781 1469045559364613730192709)
                      ·
                        rfl

theorem cell23_2860956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_2860956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2860956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2860956 prefixEnd_2860956 := by exact prefixLift 2860956
  have htrace : WordTrace (prefixWord ++ tailWord_2860956) baseStart_2860956 baseEnd_2860956 := by
    simpa [prefixWord, tailWord_2860956, baseEnd_2860956] using wordTrace_append hprefix tailTrace_2860956
  have hstable : (prefixWord ++ tailWord_2860956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2860956).length < 2 ^ (prefixWord ++ tailWord_2860956).sum := by decide
  have hdescent : baseEnd_2860956 < baseStart_2860956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2860956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2860972 : List Nat := [2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 3]
def baseStart_2860972 : Nat := 118140960795 + 2860972 * 2 ^ 59
def prefixEnd_2860972 : Nat := 4983230072969 + 3 ^ 40 * 2860972 * 2
def baseEnd_2860972 : Nat := 1469053775055085667592635

theorem tailTrace_2860972 : CollatzResearch.WordTrace tailWord_2860972 prefixEnd_2860972 1469053775055085667592635 := by
  unfold tailWord_2860972
  simp only [CollatzResearch.WordTrace]
  refine ⟨52174110695597266981036585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69565480927463022641382113 52174110695597266981036585)
  ·
    refine ⟨39130583021697950235777439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52174110695597266981036585 39130583021697950235777439)
    ·
      refine ⟨58695874532546925353666159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39130583021697950235777439 58695874532546925353666159)
      ·
        refine ⟨88043811798820388030499239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58695874532546925353666159 88043811798820388030499239)
        ·
          refine ⟨132065717698230582045748859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88043811798820388030499239 132065717698230582045748859)
          ·
            refine ⟨198098576547345873068623289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132065717698230582045748859 198098576547345873068623289)
            ·
              refine ⟨148573932410509404801467467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 198098576547345873068623289 148573932410509404801467467)
              ·
                refine ⟨222860898615764107202201201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148573932410509404801467467 222860898615764107202201201)
                ·
                  refine ⟨167145673961823080401650901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 222860898615764107202201201 167145673961823080401650901)
                  ·
                    refine ⟨3917476733480228446913693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 167145673961823080401650901 3917476733480228446913693)
                    ·
                      refine ⟨1469053775055085667592635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3917476733480228446913693 1469053775055085667592635)
                      ·
                        rfl

theorem cell23_2860972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 3].length) (baseStart_2860972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2860972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2860972 prefixEnd_2860972 := by exact prefixLift 2860972
  have htrace : WordTrace (prefixWord ++ tailWord_2860972) baseStart_2860972 baseEnd_2860972 := by
    simpa [prefixWord, tailWord_2860972, baseEnd_2860972] using wordTrace_append hprefix tailTrace_2860972
  have hstable : (prefixWord ++ tailWord_2860972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2860972).length < 2 ^ (prefixWord ++ tailWord_2860972).sum := by decide
  have hdescent : baseEnd_2860972 < baseStart_2860972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2860972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861002 : List Nat := [3, 1, 2, 1, 2, 1, 2, 1, 1, 4, 5]
def baseStart_2861002 : Nat := 118140960795 + 2861002 * 2 ^ 59
def prefixEnd_2861002 : Nat := 4983230072969 + 3 ^ 40 * 2861002 * 2
def baseEnd_2861002 : Nat := 1469069179474720550217497

theorem tailTrace_2861002 : CollatzResearch.WordTrace tailWord_2861002 prefixEnd_2861002 1469069179474720550217497 := by
  unfold tailWord_2861002
  simp only [CollatzResearch.WordTrace]
  refine ⟨26087328895271462271416315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69566210387390566057110173 26087328895271462271416315)
  ·
    refine ⟨39130993342907193407124473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26087328895271462271416315 39130993342907193407124473)
    ·
      refine ⟨29348245007180395055343355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39130993342907193407124473 29348245007180395055343355)
      ·
        refine ⟨44022367510770592583015033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29348245007180395055343355 44022367510770592583015033)
        ·
          refine ⟨33016775633077944437261275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44022367510770592583015033 33016775633077944437261275)
          ·
            refine ⟨49525163449616916655891913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33016775633077944437261275 49525163449616916655891913)
            ·
              refine ⟨37143872587212687491918935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49525163449616916655891913 37143872587212687491918935)
              ·
                refine ⟨55715808880819031237878403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37143872587212687491918935 55715808880819031237878403)
                ·
                  refine ⟨83573713321228546856817605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55715808880819031237878403 83573713321228546856817605)
                  ·
                    refine ⟨15670071247730352535653301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 83573713321228546856817605 15670071247730352535653301)
                    ·
                      refine ⟨1469069179474720550217497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15670071247730352535653301 1469069179474720550217497)
                      ·
                        rfl

theorem cell23_2861002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 1, 4, 5].length) (baseStart_2861002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2861002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2861002 prefixEnd_2861002 := by exact prefixLift 2861002
  have htrace : WordTrace (prefixWord ++ tailWord_2861002) baseStart_2861002 baseEnd_2861002 := by
    simpa [prefixWord, tailWord_2861002, baseEnd_2861002] using wordTrace_append hprefix tailTrace_2861002
  have hstable : (prefixWord ++ tailWord_2861002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861002).length < 2 ^ (prefixWord ++ tailWord_2861002).sum := by decide
  have hdescent : baseEnd_2861002 < baseStart_2861002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861010 : List Nat := [3, 2, 2, 3, 2, 1, 3, 1, 1, 2, 3]
def baseStart_2861010 : Nat := 118140960795 + 2861010 * 2 ^ 59
def prefixEnd_2861010 : Nat := 4983230072969 + 3 ^ 40 * 2861010 * 2
def baseEnd_2861010 : Nat := 1469073287319956518917461

theorem tailTrace_2861010 : CollatzResearch.WordTrace tailWord_2861010 prefixEnd_2861010 1469073287319956518917461 := by
  unfold tailWord_2861010
  simp only [CollatzResearch.WordTrace]
  refine ⟨26087401841264216612989121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69566404910037910967970989 26087401841264216612989121)
  ·
    refine ⟨19565551380948162459741841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26087401841264216612989121 19565551380948162459741841)
    ·
      refine ⟨14674163535711121844806381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19565551380948162459741841 14674163535711121844806381)
      ·
        refine ⟨5502811325891670691802393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14674163535711121844806381 5502811325891670691802393)
        ·
          refine ⟨4127108494418753018851795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5502811325891670691802393 4127108494418753018851795)
          ·
            refine ⟨6190662741628129528277693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4127108494418753018851795 6190662741628129528277693)
            ·
              refine ⟨2321498528110548573104135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6190662741628129528277693 2321498528110548573104135)
              ·
                refine ⟨3482247792165822859656203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2321498528110548573104135 3482247792165822859656203)
                ·
                  refine ⟨5223371688248734289484305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3482247792165822859656203 5223371688248734289484305)
                  ·
                    refine ⟨3917528766186550717113229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5223371688248734289484305 3917528766186550717113229)
                    ·
                      refine ⟨1469073287319956518917461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3917528766186550717113229 1469073287319956518917461)
                      ·
                        rfl

theorem cell23_2861010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_2861010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2861010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2861010 prefixEnd_2861010 := by exact prefixLift 2861010
  have htrace : WordTrace (prefixWord ++ tailWord_2861010) baseStart_2861010 baseEnd_2861010 := by
    simpa [prefixWord, tailWord_2861010, baseEnd_2861010] using wordTrace_append hprefix tailTrace_2861010
  have hstable : (prefixWord ++ tailWord_2861010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861010).length < 2 ^ (prefixWord ++ tailWord_2861010).sum := by decide
  have hdescent : baseEnd_2861010 < baseStart_2861010 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861023 : List Nat := [1, 1, 2, 3, 4, 2, 2, 2, 2, 1, 3]
def baseStart_2861023 : Nat := 118140960795 + 2861023 * 2 ^ 59
def prefixEnd_2861023 : Nat := 4983230072969 + 3 ^ 40 * 2861023 * 2
def baseEnd_2861023 : Nat := 1469079962568464968054901

theorem tailTrace_2861023 : CollatzResearch.WordTrace tailWord_2861023 prefixEnd_2861023 1469079962568464968054901 := by
  unfold tailWord_2861023
  simp only [CollatzResearch.WordTrace]
  refine ⟨104350081514009769672179723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69566721009339846448119815 104350081514009769672179723)
  ·
    refine ⟨156525122271014654508269585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104350081514009769672179723 156525122271014654508269585)
    ·
      refine ⟨117393841703260990881202189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156525122271014654508269585 117393841703260990881202189)
      ·
        refine ⟨44022690638722871580450821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117393841703260990881202189 44022690638722871580450821)
        ·
          refine ⟨8254254494760538421334529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44022690638722871580450821 8254254494760538421334529)
          ·
            refine ⟨6190690871070403816000897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8254254494760538421334529 6190690871070403816000897)
            ·
              refine ⟨4643018153302802862000673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6190690871070403816000897 4643018153302802862000673)
              ·
                refine ⟨3482263614977102146500505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4643018153302802862000673 3482263614977102146500505)
                ·
                  refine ⟨2611697711232826609875379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3482263614977102146500505 2611697711232826609875379)
                  ·
                    refine ⟨3917546566849239914813069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2611697711232826609875379 3917546566849239914813069)
                    ·
                      refine ⟨1469079962568464968054901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3917546566849239914813069 1469079962568464968054901)
                      ·
                        rfl

theorem cell23_2861023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 2, 2, 1, 3].length) (baseStart_2861023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2861023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2861023 prefixEnd_2861023 := by exact prefixLift 2861023
  have htrace : WordTrace (prefixWord ++ tailWord_2861023) baseStart_2861023 baseEnd_2861023 := by
    simpa [prefixWord, tailWord_2861023, baseEnd_2861023] using wordTrace_append hprefix tailTrace_2861023
  have hstable : (prefixWord ++ tailWord_2861023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861023).length < 2 ^ (prefixWord ++ tailWord_2861023).sum := by decide
  have hdescent : baseEnd_2861023 < baseStart_2861023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861119 : List Nat := [1, 1, 2, 2, 3, 1, 4, 1, 1, 3, 4]
def baseStart_2861119 : Nat := 118140960795 + 2861119 * 2 ^ 59
def prefixEnd_2861119 : Nat := 4983230072969 + 3 ^ 40 * 2861119 * 2
def baseEnd_2861119 : Nat := 1469129256711296592454459

theorem tailTrace_2861119 : CollatzResearch.WordTrace tailWord_2861119 prefixEnd_2861119 1469129256711296592454459 := by
  unfold tailWord_2861119
  simp only [CollatzResearch.WordTrace]
  refine ⟨104353582921661978067674411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69569055281107985378449607 104353582921661978067674411)
  ·
    refine ⟨156530374382492967101511617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104353582921661978067674411 156530374382492967101511617)
    ·
      refine ⟨117397780786869725326133713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156530374382492967101511617 117397780786869725326133713)
      ·
        refine ⟨88048335590152293994600285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117397780786869725326133713 88048335590152293994600285)
        ·
          refine ⟨33018125846307110247975107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88048335590152293994600285 33018125846307110247975107)
          ·
            refine ⟨49527188769460665371962661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33018125846307110247975107 49527188769460665371962661)
            ·
              refine ⟨9286347894273874757242999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49527188769460665371962661 9286347894273874757242999)
              ·
                refine ⟨13929521841410812135864499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9286347894273874757242999 13929521841410812135864499)
                ·
                  refine ⟨20894282762116218203796749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13929521841410812135864499 20894282762116218203796749)
                  ·
                    refine ⟨7835356035793581826423781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20894282762116218203796749 7835356035793581826423781)
                    ·
                      refine ⟨1469129256711296592454459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7835356035793581826423781 1469129256711296592454459)
                      ·
                        rfl

theorem cell23_2861119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 3, 4].length) (baseStart_2861119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2861119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2861119 prefixEnd_2861119 := by exact prefixLift 2861119
  have htrace : WordTrace (prefixWord ++ tailWord_2861119) baseStart_2861119 baseEnd_2861119 := by
    simpa [prefixWord, tailWord_2861119, baseEnd_2861119] using wordTrace_append hprefix tailTrace_2861119
  have hstable : (prefixWord ++ tailWord_2861119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861119).length < 2 ^ (prefixWord ++ tailWord_2861119).sum := by decide
  have hdescent : baseEnd_2861119 < baseStart_2861119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861196 : List Nat := [2, 2, 1, 2, 1, 1, 1, 1, 5, 5, 2]
def baseStart_2861196 : Nat := 118140960795 + 2861196 * 2 ^ 59
def prefixEnd_2861196 : Nat := 4983230072969 + 3 ^ 40 * 2861196 * 2
def baseEnd_2861196 : Nat := 1469168794721692791191605

theorem tailTrace_2861196 : CollatzResearch.WordTrace tailWord_2861196 prefixEnd_2861196 1469168794721692791191605 := by
  unfold tailWord_2861196
  simp only [CollatzResearch.WordTrace]
  refine ⟨52178195671191510109113721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69570927561588680145484961 52178195671191510109113721)
  ·
    refine ⟨39133646753393632581835291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52178195671191510109113721 39133646753393632581835291)
    ·
      refine ⟨58700470130090448872752937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39133646753393632581835291 58700470130090448872752937)
      ·
        refine ⟨44025352597567836654564703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58700470130090448872752937 44025352597567836654564703)
        ·
          refine ⟨66038028896351754981847055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44025352597567836654564703 66038028896351754981847055)
          ·
            refine ⟨99057043344527632472770583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66038028896351754981847055 99057043344527632472770583)
            ·
              refine ⟨148585565016791448709155875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99057043344527632472770583 148585565016791448709155875)
              ·
                refine ⟨222878347525187173063733813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148585565016791448709155875 222878347525187173063733813)
                ·
                  refine ⟨20894845080486297474725045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 222878347525187173063733813 20894845080486297474725045)
                  ·
                    refine ⟨1958891726295590388255473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20894845080486297474725045 1958891726295590388255473)
                    ·
                      refine ⟨1469168794721692791191605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1958891726295590388255473 1469168794721692791191605)
                      ·
                        rfl

theorem cell23_2861196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 5, 5, 2].length) (baseStart_2861196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2861196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2861196 prefixEnd_2861196 := by exact prefixLift 2861196
  have htrace : WordTrace (prefixWord ++ tailWord_2861196) baseStart_2861196 baseEnd_2861196 := by
    simpa [prefixWord, tailWord_2861196, baseEnd_2861196] using wordTrace_append hprefix tailTrace_2861196
  have hstable : (prefixWord ++ tailWord_2861196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861196).length < 2 ^ (prefixWord ++ tailWord_2861196).sum := by decide
  have hdescent : baseEnd_2861196 < baseStart_2861196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861220 : List Nat := [2, 3, 1, 2, 4, 1, 1, 2, 3, 1, 3]
def baseStart_2861220 : Nat := 118140960795 + 2861220 * 2 ^ 59
def prefixEnd_2861220 : Nat := 4983230072969 + 3 ^ 40 * 2861220 * 2
def baseEnd_2861220 : Nat := 1469181118257400697291495

theorem tailTrace_2861220 : CollatzResearch.WordTrace tailWord_2861220 prefixEnd_2861220 1469181118257400697291495 := by
  unfold tailWord_2861220
  simp only [CollatzResearch.WordTrace]
  refine ⟨52178633347148036158550557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69571511129530714878067409 52178633347148036158550557)
  ·
    refine ⟨19566987505180513559456459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52178633347148036158550557 19566987505180513559456459)
    ·
      refine ⟨29350481257770770339184689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19566987505180513559456459 29350481257770770339184689)
      ·
        refine ⟨22012860943328077754388517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29350481257770770339184689 22012860943328077754388517)
        ·
          refine ⟨4127411426874014578947847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22012860943328077754388517 4127411426874014578947847)
          ·
            refine ⟨6191117140311021868421771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4127411426874014578947847 6191117140311021868421771)
            ·
              refine ⟨9286675710466532802632657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6191117140311021868421771 9286675710466532802632657)
              ·
                refine ⟨6965006782849899601974493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9286675710466532802632657 6965006782849899601974493)
                ·
                  refine ⟨2611877543568712350740435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6965006782849899601974493 2611877543568712350740435)
                  ·
                    refine ⟨3917816315353068526110653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2611877543568712350740435 3917816315353068526110653)
                    ·
                      refine ⟨1469181118257400697291495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3917816315353068526110653 1469181118257400697291495)
                      ·
                        rfl

theorem cell23_2861220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 2, 3, 1, 3].length) (baseStart_2861220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2861220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2861220 prefixEnd_2861220 := by exact prefixLift 2861220
  have htrace : WordTrace (prefixWord ++ tailWord_2861220) baseStart_2861220 baseEnd_2861220 := by
    simpa [prefixWord, tailWord_2861220, baseEnd_2861220] using wordTrace_append hprefix tailTrace_2861220
  have hstable : (prefixWord ++ tailWord_2861220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861220).length < 2 ^ (prefixWord ++ tailWord_2861220).sum := by decide
  have hdescent : baseEnd_2861220 < baseStart_2861220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861243 : List Nat := [1, 1, 1, 1, 1, 2, 5, 2, 5, 2, 2]
def baseStart_2861243 : Nat := 118140960795 + 2861243 * 2 ^ 59
def prefixEnd_2861243 : Nat := 4983230072969 + 3 ^ 40 * 2861243 * 2
def baseEnd_2861243 : Nat := 1469192928312454107303889

theorem tailTrace_2861243 : CollatzResearch.WordTrace tailWord_2861243 prefixEnd_2861243 1469192928312454107303889 := by
  unfold tailWord_2861243
  simp only [CollatzResearch.WordTrace]
  refine ⟨104358105573212747245188383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69572070382141831496792255 104358105573212747245188383)
  ·
    refine ⟨156537158359819120867782575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104358105573212747245188383 156537158359819120867782575)
    ·
      refine ⟨234805737539728681301673863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156537158359819120867782575 234805737539728681301673863)
      ·
        refine ⟨352208606309593021952510795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234805737539728681301673863 352208606309593021952510795)
        ·
          refine ⟨528312909464389532928766193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 352208606309593021952510795 528312909464389532928766193)
          ·
            refine ⟨396234682098292149696574645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 528312909464389532928766193 396234682098292149696574645)
            ·
              refine ⟨37147001446714889034053873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 396234682098292149696574645 37147001446714889034053873)
              ·
                refine ⟨27860251085036166775540405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37147001446714889034053873 27860251085036166775540405)
                ·
                  refine ⟨2611898539222140635206913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27860251085036166775540405 2611898539222140635206913)
                  ·
                    refine ⟨1958923904416605476405185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2611898539222140635206913 1958923904416605476405185)
                    ·
                      refine ⟨1469192928312454107303889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1958923904416605476405185 1469192928312454107303889)
                      ·
                        rfl

theorem cell23_2861243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 5, 2, 2].length) (baseStart_2861243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2861243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2861243 prefixEnd_2861243 := by exact prefixLift 2861243
  have htrace : WordTrace (prefixWord ++ tailWord_2861243) baseStart_2861243 baseEnd_2861243 := by
    simpa [prefixWord, tailWord_2861243, baseEnd_2861243] using wordTrace_append hprefix tailTrace_2861243
  have hstable : (prefixWord ++ tailWord_2861243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861243).length < 2 ^ (prefixWord ++ tailWord_2861243).sum := by decide
  have hdescent : baseEnd_2861243 < baseStart_2861243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861253 : List Nat := [1, 3, 1, 1, 1, 1, 7, 2, 2, 4]
def baseStart_2861253 : Nat := 118140960795 + 2861253 * 2 ^ 59
def prefixEnd_2861253 : Nat := 4983230072969 + 3 ^ 40 * 2861253 * 2
def baseEnd_2861253 : Nat := 489732687706333022726281

theorem tailTrace_2861253 : CollatzResearch.WordTrace tailWord_2861253 prefixEnd_2861253 489732687706333022726281 := by
  unfold tailWord_2861253
  simp only [CollatzResearch.WordTrace]
  refine ⟨104358470303176518953052413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69572313535451012635368275 104358470303176518953052413)
  ·
    refine ⟨39134426363691194607394655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104358470303176518953052413 39134426363691194607394655)
    ·
      refine ⟨58701639545536791911091983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39134426363691194607394655 58701639545536791911091983)
      ·
        refine ⟨88052459318305187866637975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58701639545536791911091983 88052459318305187866637975)
        ·
          refine ⟨132078688977457781799956963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88052459318305187866637975 132078688977457781799956963)
          ·
            refine ⟨198118033466186672699935445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132078688977457781799956963 198118033466186672699935445)
            ·
              refine ⟨4643391409363750141404737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 198118033466186672699935445 4643391409363750141404737)
              ·
                refine ⟨3482543557022812606053553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4643391409363750141404737 3482543557022812606053553)
                ·
                  refine ⟨2611907667767109454540165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3482543557022812606053553 2611907667767109454540165)
                  ·
                    refine ⟨489732687706333022726281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2611907667767109454540165 489732687706333022726281)
                    ·
                      rfl

theorem cell23_2861253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 2, 2, 4].length) (baseStart_2861253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2861253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2861253 prefixEnd_2861253 := by exact prefixLift 2861253
  have htrace : WordTrace (prefixWord ++ tailWord_2861253) baseStart_2861253 baseEnd_2861253 := by
    simpa [prefixWord, tailWord_2861253, baseEnd_2861253] using wordTrace_append hprefix tailTrace_2861253
  have hstable : (prefixWord ++ tailWord_2861253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861253).length < 2 ^ (prefixWord ++ tailWord_2861253).sum := by decide
  have hdescent : baseEnd_2861253 < baseStart_2861253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861270 : List Nat := [5, 2, 1, 2, 1, 1, 3, 1, 1, 6]
def baseStart_2861270 : Nat := 118140960795 + 2861270 * 2 ^ 59
def prefixEnd_2861270 : Nat := 4983230072969 + 3 ^ 40 * 2861270 * 2
def baseEnd_2861270 : Nat := 489735597430041833888755

theorem tailTrace_2861270 : CollatzResearch.WordTrace tailWord_2861270 prefixEnd_2861270 489735597430041833888755 := by
  unfold tailWord_2861270
  simp only [CollatzResearch.WordTrace]
  refine ⟨6522443146507183178526329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69572726896076620570947509 6522443146507183178526329)
  ·
    refine ⟨4891832359880387383894747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6522443146507183178526329 4891832359880387383894747)
    ·
      refine ⟨7337748539820581075842121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4891832359880387383894747 7337748539820581075842121)
      ·
        refine ⟨5503311404865435806881591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7337748539820581075842121 5503311404865435806881591)
        ·
          refine ⟨8254967107298153710322387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5503311404865435806881591 8254967107298153710322387)
          ·
            refine ⟨12382450660947230565483581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8254967107298153710322387 12382450660947230565483581)
            ·
              refine ⟨4643418997855211462056343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12382450660947230565483581 4643418997855211462056343)
              ·
                refine ⟨6965128496782817193084515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4643418997855211462056343 6965128496782817193084515)
                ·
                  refine ⟨10447692745174225789626773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6965128496782817193084515 10447692745174225789626773)
                  ·
                    refine ⟨489735597430041833888755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10447692745174225789626773 489735597430041833888755)
                    ·
                      rfl

theorem cell23_2861270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_2861270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2861270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2861270 prefixEnd_2861270 := by exact prefixLift 2861270
  have htrace : WordTrace (prefixWord ++ tailWord_2861270) baseStart_2861270 baseEnd_2861270 := by
    simpa [prefixWord, tailWord_2861270, baseEnd_2861270] using wordTrace_append hprefix tailTrace_2861270
  have hstable : (prefixWord ++ tailWord_2861270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861270).length < 2 ^ (prefixWord ++ tailWord_2861270).sum := by decide
  have hdescent : baseEnd_2861270 < baseStart_2861270 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861277 : List Nat := [1, 4, 3, 2, 1, 1, 2, 2, 3, 2, 2]
def baseStart_2861277 : Nat := 118140960795 + 2861277 * 2 ^ 59
def prefixEnd_2861277 : Nat := 4983230072969 + 3 ^ 40 * 2861277 * 2
def baseEnd_2861277 : Nat := 1469210386654706974278733

theorem tailTrace_2861277 : CollatzResearch.WordTrace tailWord_2861277 prefixEnd_2861277 1469210386654706974278733 := by
  unfold tailWord_2861277
  simp only [CollatzResearch.WordTrace]
  refine ⟨104359345655089571051926085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69572897103393047367950723 104359345655089571051926085)
  ·
    refine ⟨19567377310329294572236141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104359345655089571051926085 19567377310329294572236141)
    ·
      refine ⟨7337766491373485464588553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19567377310329294572236141 7337766491373485464588553)
      ·
        refine ⟨5503324868530114098441415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7337766491373485464588553 5503324868530114098441415)
        ·
          refine ⟨8254987302795171147662123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5503324868530114098441415 8254987302795171147662123)
          ·
            refine ⟨12382480954192756721493185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8254987302795171147662123 12382480954192756721493185)
            ·
              refine ⟨9286860715644567541119889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12382480954192756721493185 9286860715644567541119889)
              ·
                refine ⟨6965145536733425655839917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9286860715644567541119889 6965145536733425655839917)
                ·
                  refine ⟨2611929576275034620939969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6965145536733425655839917 2611929576275034620939969)
                  ·
                    refine ⟨1958947182206275965704977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2611929576275034620939969 1958947182206275965704977)
                    ·
                      refine ⟨1469210386654706974278733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1958947182206275965704977 1469210386654706974278733)
                      ·
                        rfl

theorem cell23_2861277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_2861277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2861277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2861277 prefixEnd_2861277 := by exact prefixLift 2861277
  have htrace : WordTrace (prefixWord ++ tailWord_2861277) baseStart_2861277 baseEnd_2861277 := by
    simpa [prefixWord, tailWord_2861277, baseEnd_2861277] using wordTrace_append hprefix tailTrace_2861277
  have hstable : (prefixWord ++ tailWord_2861277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861277).length < 2 ^ (prefixWord ++ tailWord_2861277).sum := by decide
  have hdescent : baseEnd_2861277 < baseStart_2861277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861283 : List Nat := [1, 1, 1, 8, 1, 1, 1, 9]
def baseStart_2861283 : Nat := 118140960795 + 2861283 * 2 ^ 59
def prefixEnd_2861283 : Nat := 4983230072969 + 3 ^ 40 * 2861283 * 2
def baseEnd_2861283 : Nat := 54415313612541998177915

theorem tailTrace_2861283 : CollatzResearch.WordTrace tailWord_2861283 prefixEnd_2861283 54415313612541998177915 := by
  unfold tailWord_2861283
  simp only [CollatzResearch.WordTrace]
  refine ⟨104359564493067834076644503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69573042995378556051096335 104359564493067834076644503)
  ·
    refine ⟨156539346739601751114966755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104359564493067834076644503 156539346739601751114966755)
    ·
      refine ⟨234809020109402626672450133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156539346739601751114966755 234809020109402626672450133)
      ·
        refine ⟨2751668204407062031317775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 234809020109402626672450133 2751668204407062031317775)
        ·
          refine ⟨4127502306610593046976663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2751668204407062031317775 4127502306610593046976663)
          ·
            refine ⟨6191253459915889570464995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4127502306610593046976663 6191253459915889570464995)
            ·
              refine ⟨9286880189873834355697493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6191253459915889570464995 9286880189873834355697493)
              ·
                refine ⟨54415313612541998177915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9286880189873834355697493 54415313612541998177915)
                ·
                  rfl

theorem cell23_2861283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 9].length) (baseStart_2861283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2861283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2861283 prefixEnd_2861283 := by exact prefixLift 2861283
  have htrace : WordTrace (prefixWord ++ tailWord_2861283) baseStart_2861283 baseEnd_2861283 := by
    simpa [prefixWord, tailWord_2861283, baseEnd_2861283] using wordTrace_append hprefix tailTrace_2861283
  have hstable : (prefixWord ++ tailWord_2861283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861283).length < 2 ^ (prefixWord ++ tailWord_2861283).sum := by decide
  have hdescent : baseEnd_2861283 < baseStart_2861283 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861310 : List Nat := [4, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3]
def baseStart_2861310 : Nat := 118140960795 + 2861310 * 2 ^ 59
def prefixEnd_2861310 : Nat := 4983230072969 + 3 ^ 40 * 2861310 * 2
def baseEnd_2861310 : Nat := 1469227331516305345166081

theorem tailTrace_2861310 : CollatzResearch.WordTrace tailWord_2861310 prefixEnd_2861310 1469227331516305345166081 := by
  unfold tailWord_2861310
  simp only [CollatzResearch.WordTrace]
  refine ⟨13045068657996252210984673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69573699509313345125251589 13045068657996252210984673)
  ·
    refine ⟨9783801493497189158238505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13045068657996252210984673 9783801493497189158238505)
    ·
      refine ⟨7337851120122891868678879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9783801493497189158238505 7337851120122891868678879)
      ·
        refine ⟨11006776680184337803018319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7337851120122891868678879 11006776680184337803018319)
        ·
          refine ⟨16510165020276506704527479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11006776680184337803018319 16510165020276506704527479)
          ·
            refine ⟨24765247530414760056791219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16510165020276506704527479 24765247530414760056791219)
            ·
              refine ⟨37147871295622140085186829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24765247530414760056791219 37147871295622140085186829)
              ·
                refine ⟨13930451735858302531945061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37147871295622140085186829 13930451735858302531945061)
                ·
                  refine ⟨2611959700473431724739699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13930451735858302531945061 2611959700473431724739699)
                  ·
                    refine ⟨3917939550710147587109549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2611959700473431724739699 3917939550710147587109549)
                    ·
                      refine ⟨1469227331516305345166081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3917939550710147587109549 1469227331516305345166081)
                      ·
                        rfl

theorem cell23_2861310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_2861310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2861310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2861310 prefixEnd_2861310 := by exact prefixLift 2861310
  have htrace : WordTrace (prefixWord ++ tailWord_2861310) baseStart_2861310 baseEnd_2861310 := by
    simpa [prefixWord, tailWord_2861310, baseEnd_2861310] using wordTrace_append hprefix tailTrace_2861310
  have hstable : (prefixWord ++ tailWord_2861310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861310).length < 2 ^ (prefixWord ++ tailWord_2861310).sum := by decide
  have hdescent : baseEnd_2861310 < baseStart_2861310 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861326 : List Nat := [4, 1, 1, 2, 1, 2, 2, 1, 1, 8]
def baseStart_2861326 : Nat := 118140960795 + 2861326 * 2 ^ 59
def prefixEnd_2861326 : Nat := 4983230072969 + 3 ^ 40 * 2861326 * 2
def baseEnd_2861326 : Nat := 489745182402259094188669

theorem tailTrace_2861326 : CollatzResearch.WordTrace tailWord_2861326 prefixEnd_2861326 489745182402259094188669 := by
  unfold tailWord_2861326
  simp only [CollatzResearch.WordTrace]
  refine ⟨13045141603989006552557479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69574088554608034946973221 13045141603989006552557479)
  ·
    refine ⟨19567712405983509828836219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13045141603989006552557479 19567712405983509828836219)
    ·
      refine ⟨29351568608975264743254329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19567712405983509828836219 29351568608975264743254329)
      ·
        refine ⟨22013676456731448557440747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29351568608975264743254329 22013676456731448557440747)
        ·
          refine ⟨33020514685097172836161121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22013676456731448557440747 33020514685097172836161121)
          ·
            refine ⟨24765386013822879627120841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33020514685097172836161121 24765386013822879627120841)
            ·
              refine ⟨18574039510367159720340631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24765386013822879627120841 18574039510367159720340631)
              ·
                refine ⟨27861059265550739580510947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18574039510367159720340631 27861059265550739580510947)
                ·
                  refine ⟨41791588898326109370766421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27861059265550739580510947 41791588898326109370766421)
                  ·
                    refine ⟨489745182402259094188669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 41791588898326109370766421 489745182402259094188669)
                    ·
                      rfl

theorem cell23_2861326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 1, 8].length) (baseStart_2861326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2861326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2861326 prefixEnd_2861326 := by exact prefixLift 2861326
  have htrace : WordTrace (prefixWord ++ tailWord_2861326) baseStart_2861326 baseEnd_2861326 := by
    simpa [prefixWord, tailWord_2861326, baseEnd_2861326] using wordTrace_append hprefix tailTrace_2861326
  have hstable : (prefixWord ++ tailWord_2861326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861326).length < 2 ^ (prefixWord ++ tailWord_2861326).sum := by decide
  have hdescent : baseEnd_2861326 < baseStart_2861326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861336 : List Nat := [2, 1, 2, 3, 1, 2, 1, 1, 4, 1, 5]
def baseStart_2861336 : Nat := 118140960795 + 2861336 * 2 ^ 59
def prefixEnd_2861336 : Nat := 4983230072969 + 3 ^ 40 * 2861336 * 2
def baseEnd_2861336 : Nat := 1469240682013322243440961

theorem tailTrace_2861336 : CollatzResearch.WordTrace tailWord_2861336 prefixEnd_2861336 1469240682013322243440961 := by
  unfold tailWord_2861336
  simp only [CollatzResearch.WordTrace]
  refine ⟨52180748780937912064161931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69574331707917216085549241 52180748780937912064161931)
  ·
    refine ⟨78271123171406868096242897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52180748780937912064161931 78271123171406868096242897)
    ·
      refine ⟨58703342378555151072182173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78271123171406868096242897 58703342378555151072182173)
      ·
        refine ⟨22013753391958181652068315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58703342378555151072182173 22013753391958181652068315)
        ·
          refine ⟨33020630087937272478102473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22013753391958181652068315 33020630087937272478102473)
          ·
            refine ⟨24765472565952954358576855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33020630087937272478102473 24765472565952954358576855)
            ·
              refine ⟨37148208848929431537865283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24765472565952954358576855 37148208848929431537865283)
              ·
                refine ⟨55722313273394147306797925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37148208848929431537865283 55722313273394147306797925)
                ·
                  refine ⟨10447933738761402620024611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55722313273394147306797925 10447933738761402620024611)
                  ·
                    refine ⟨15671900608142103930036917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10447933738761402620024611 15671900608142103930036917)
                    ·
                      refine ⟨1469240682013322243440961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15671900608142103930036917 1469240682013322243440961)
                      ·
                        rfl

theorem cell23_2861336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_2861336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2861336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2861336 prefixEnd_2861336 := by exact prefixLift 2861336
  have htrace : WordTrace (prefixWord ++ tailWord_2861336) baseStart_2861336 baseEnd_2861336 := by
    simpa [prefixWord, tailWord_2861336, baseEnd_2861336] using wordTrace_append hprefix tailTrace_2861336
  have hstable : (prefixWord ++ tailWord_2861336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861336).length < 2 ^ (prefixWord ++ tailWord_2861336).sum := by decide
  have hdescent : baseEnd_2861336 < baseStart_2861336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861383 : List Nat := [1, 1, 4, 1, 2, 2, 3, 1, 2, 3, 3]
def baseStart_2861383 : Nat := 118140960795 + 2861383 * 2 ^ 59
def prefixEnd_2861383 : Nat := 4983230072969 + 3 ^ 40 * 2861383 * 2
def baseEnd_2861383 : Nat := 1469264815604083559553245

theorem tailTrace_2861383 : CollatzResearch.WordTrace tailWord_2861383 prefixEnd_2861383 1469264815604083559553245 := by
  unfold tailWord_2861383
  simp only [CollatzResearch.WordTrace]
  refine ⟨104363211792705551155284803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69575474528470367436856535 104363211792705551155284803)
  ·
    refine ⟨156544817689058326732927205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104363211792705551155284803 156544817689058326732927205)
    ·
      refine ⟨29352153316698436262423851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 156544817689058326732927205 29352153316698436262423851)
      ·
        refine ⟨44028229975047654393635777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29352153316698436262423851 44028229975047654393635777)
        ·
          refine ⟨33021172481285740795226833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44028229975047654393635777 33021172481285740795226833)
          ·
            refine ⟨24765879360964305596420125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33021172481285740795226833 24765879360964305596420125)
            ·
              refine ⟨9287204760361614598657547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24765879360964305596420125 9287204760361614598657547)
              ·
                refine ⟨13930807140542421897986321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9287204760361614598657547 13930807140542421897986321)
                ·
                  refine ⟨10448105355406816423489741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13930807140542421897986321 10448105355406816423489741)
                  ·
                    refine ⟨3918039508277556158808653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10448105355406816423489741 3918039508277556158808653)
                    ·
                      refine ⟨1469264815604083559553245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3918039508277556158808653 1469264815604083559553245)
                      ·
                        rfl

theorem cell23_2861383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 2, 3, 3].length) (baseStart_2861383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2861383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2861383 prefixEnd_2861383 := by exact prefixLift 2861383
  have htrace : WordTrace (prefixWord ++ tailWord_2861383) baseStart_2861383 baseEnd_2861383 := by
    simpa [prefixWord, tailWord_2861383, baseEnd_2861383] using wordTrace_append hprefix tailTrace_2861383
  have hstable : (prefixWord ++ tailWord_2861383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861383).length < 2 ^ (prefixWord ++ tailWord_2861383).sum := by decide
  have hdescent : baseEnd_2861383 < baseStart_2861383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861480 : List Nat := [2, 1, 6, 1, 1, 1, 2, 1, 8]
def baseStart_2861480 : Nat := 118140960795 + 2861480 * 2 ^ 59
def prefixEnd_2861480 : Nat := 4983230072969 + 3 ^ 40 * 2861480 * 2
def baseEnd_2861480 : Nat := 163257180358618853337811

theorem tailTrace_2861480 : CollatzResearch.WordTrace tailWord_2861480 prefixEnd_2861480 163257180358618853337811 := by
  unfold tailWord_2861480
  simp only [CollatzResearch.WordTrace]
  refine ⟨52183374836677068360782947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69577833115569424481043929 52183374836677068360782947)
  ·
    refine ⟨78275062255015602541174421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52183374836677068360782947 78275062255015602541174421)
    ·
      refine ⟨3669143543203856369117551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 78275062255015602541174421 3669143543203856369117551)
      ·
        refine ⟨5503715314805784553676327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3669143543203856369117551 5503715314805784553676327)
        ·
          refine ⟨8255572972208676830514491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5503715314805784553676327 8255572972208676830514491)
          ·
            refine ⟨12383359458313015245771737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8255572972208676830514491 12383359458313015245771737)
            ·
              refine ⟨9287519593734761434328803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12383359458313015245771737 9287519593734761434328803)
              ·
                refine ⟨13931279390602142151493205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9287519593734761434328803 13931279390602142151493205)
                ·
                  refine ⟨163257180358618853337811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13931279390602142151493205 163257180358618853337811)
                  ·
                    rfl

theorem cell23_2861480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 8].length) (baseStart_2861480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2861480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2861480 prefixEnd_2861480 := by exact prefixLift 2861480
  have htrace : WordTrace (prefixWord ++ tailWord_2861480) baseStart_2861480 baseEnd_2861480 := by
    simpa [prefixWord, tailWord_2861480, baseEnd_2861480] using wordTrace_append hprefix tailTrace_2861480
  have hstable : (prefixWord ++ tailWord_2861480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861480).length < 2 ^ (prefixWord ++ tailWord_2861480).sum := by decide
  have hdescent : baseEnd_2861480 < baseStart_2861480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861497 : List Nat := [1, 2, 1, 4, 3, 3, 2, 1, 6]
def baseStart_2861497 : Nat := 118140960795 + 2861497 * 2 ^ 59
def prefixEnd_2861497 : Nat := 4983230072969 + 3 ^ 40 * 2861497 * 2
def baseEnd_2861497 : Nat := 163258150266521790391969

theorem tailTrace_2861497 : CollatzResearch.WordTrace tailWord_2861497 prefixEnd_2861497 163258150266521790391969 := by
  unfold tailWord_2861497
  simp only [CollatzResearch.WordTrace]
  refine ⟨104367369714292548624934745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69578246476195032416623163 104367369714292548624934745)
  ·
    refine ⟨78275527285719411468701059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104367369714292548624934745 78275527285719411468701059)
    ·
      refine ⟨117413290928579117203051589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78275527285719411468701059 117413290928579117203051589)
      ·
        refine ⟨22014992049108584475572173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 117413290928579117203051589 22014992049108584475572173)
        ·
          refine ⟨8255622018415719178339565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22014992049108584475572173 8255622018415719178339565)
          ·
            refine ⟨3095858256905894691877337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8255622018415719178339565 3095858256905894691877337)
            ·
              refine ⟨2321893692679421018908003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3095858256905894691877337 2321893692679421018908003)
              ·
                refine ⟨3482840539019131528362005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2321893692679421018908003 3482840539019131528362005)
                ·
                  refine ⟨163258150266521790391969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3482840539019131528362005 163258150266521790391969)
                  ·
                    rfl

theorem cell23_2861497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 2, 1, 6].length) (baseStart_2861497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2861497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2861497 prefixEnd_2861497 := by exact prefixLift 2861497
  have htrace : WordTrace (prefixWord ++ tailWord_2861497) baseStart_2861497 baseEnd_2861497 := by
    simpa [prefixWord, tailWord_2861497, baseEnd_2861497] using wordTrace_append hprefix tailTrace_2861497
  have hstable : (prefixWord ++ tailWord_2861497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861497).length < 2 ^ (prefixWord ++ tailWord_2861497).sum := by decide
  have hdescent : baseEnd_2861497 < baseStart_2861497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861541 : List Nat := [1, 3, 1, 5, 2, 1, 1, 4, 1, 1, 3]
def baseStart_2861541 : Nat := 118140960795 + 2861541 * 2 ^ 59
def prefixEnd_2861541 : Nat := 4983230072969 + 3 ^ 40 * 2861541 * 2
def baseEnd_2861541 : Nat := 1469345945547493941377519

theorem tailTrace_2861541 : CollatzResearch.WordTrace tailWord_2861541 prefixEnd_2861541 1469345945547493941377519 := by
  unfold tailWord_2861541
  simp only [CollatzResearch.WordTrace]
  refine ⟨104368974526133144139536477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69579316350755429426357651 104368974526133144139536477)
  ·
    refine ⟨39138365447299929052326179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104368974526133144139536477 39138365447299929052326179)
    ·
      refine ⟨58707548170949893578489269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39138365447299929052326179 58707548170949893578489269)
      ·
        refine ⟨5503832641026552522983369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58707548170949893578489269 5503832641026552522983369)
        ·
          refine ⟨4127874480769914392237527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5503832641026552522983369 4127874480769914392237527)
          ·
            refine ⟨6191811721154871588356291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4127874480769914392237527 6191811721154871588356291)
            ·
              refine ⟨9287717581732307382534437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6191811721154871588356291 9287717581732307382534437)
              ·
                refine ⟨1741447046574807634225207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9287717581732307382534437 1741447046574807634225207)
                ·
                  refine ⟨2612170569862211451337811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1741447046574807634225207 2612170569862211451337811)
                  ·
                    refine ⟨3918255854793317177006717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2612170569862211451337811 3918255854793317177006717)
                    ·
                      refine ⟨1469345945547493941377519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3918255854793317177006717 1469345945547493941377519)
                      ·
                        rfl

theorem cell23_2861541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_2861541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2861541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2861541 prefixEnd_2861541 := by exact prefixLift 2861541
  have htrace : WordTrace (prefixWord ++ tailWord_2861541) baseStart_2861541 baseEnd_2861541 := by
    simpa [prefixWord, tailWord_2861541, baseEnd_2861541] using wordTrace_append hprefix tailTrace_2861541
  have hstable : (prefixWord ++ tailWord_2861541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861541).length < 2 ^ (prefixWord ++ tailWord_2861541).sum := by decide
  have hdescent : baseEnd_2861541 < baseStart_2861541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861547 : List Nat := [1, 1, 1, 1, 2, 3, 4, 3, 3, 2, 2]
def baseStart_2861547 : Nat := 118140960795 + 2861547 * 2 ^ 59
def prefixEnd_2861547 : Nat := 4983230072969 + 3 ^ 40 * 2861547 * 2
def baseEnd_2861547 : Nat := 1469349026431420917902491

theorem tailTrace_2861547 : CollatzResearch.WordTrace tailWord_2861547 prefixEnd_2861547 1469349026431420917902491 := by
  unfold tailWord_2861547
  simp only [CollatzResearch.WordTrace]
  refine ⟨104369193364111407164254895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69579462242740938109503263 104369193364111407164254895)
  ·
    refine ⟨156553790046167110746382343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104369193364111407164254895 156553790046167110746382343)
    ·
      refine ⟨234830685069250666119573515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156553790046167110746382343 234830685069250666119573515)
      ·
        refine ⟨352246027603875999179360273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234830685069250666119573515 352246027603875999179360273)
        ·
          refine ⟨264184520702906999384520205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 352246027603875999179360273 264184520702906999384520205)
          ·
            refine ⟨99069195263590124769195077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 264184520702906999384520205 99069195263590124769195077)
            ·
              refine ⟨18575474111923148394224077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99069195263590124769195077 18575474111923148394224077)
              ·
                refine ⟨6965802791971180647834029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18575474111923148394224077 6965802791971180647834029)
                ·
                  refine ⟨2612176046989192742937761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6965802791971180647834029 2612176046989192742937761)
                  ·
                    refine ⟨1959132035241894557203321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2612176046989192742937761 1959132035241894557203321)
                    ·
                      refine ⟨1469349026431420917902491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1959132035241894557203321 1469349026431420917902491)
                      ·
                        rfl

theorem cell23_2861547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 3, 3, 2, 2].length) (baseStart_2861547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2861547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2861547 prefixEnd_2861547 := by exact prefixLift 2861547
  have htrace : WordTrace (prefixWord ++ tailWord_2861547) baseStart_2861547 baseEnd_2861547 := by
    simpa [prefixWord, tailWord_2861547, baseEnd_2861547] using wordTrace_append hprefix tailTrace_2861547
  have hstable : (prefixWord ++ tailWord_2861547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861547).length < 2 ^ (prefixWord ++ tailWord_2861547).sum := by decide
  have hdescent : baseEnd_2861547 < baseStart_2861547 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861560 : List Nat := [2, 1, 2, 1, 1, 4, 4, 1, 1, 2, 4]
def baseStart_2861560 : Nat := 118140960795 + 2861560 * 2 ^ 59
def prefixEnd_2861560 : Nat := 4983230072969 + 3 ^ 40 * 2861560 * 2
def baseEnd_2861560 : Nat := 1469355701679929367039931

theorem tailTrace_2861560 : CollatzResearch.WordTrace tailWord_2861560 prefixEnd_2861560 1469355701679929367039931 := by
  unfold tailWord_2861560
  simp only [CollatzResearch.WordTrace]
  refine ⟨52184833756532155192239067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69579778342042873589652089 52184833756532155192239067)
  ·
    refine ⟨78277250634798232788358601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52184833756532155192239067 78277250634798232788358601)
    ·
      refine ⟨58707937976098674591268951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78277250634798232788358601 58707937976098674591268951)
      ·
        refine ⟨88061906964148011886903427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58707937976098674591268951 88061906964148011886903427)
        ·
          refine ⟨132092860446222017830355141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88061906964148011886903427 132092860446222017830355141)
          ·
            refine ⟨24767411333666628343191589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 132092860446222017830355141 24767411333666628343191589)
            ·
              refine ⟨4643889625062492814348423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24767411333666628343191589 4643889625062492814348423)
              ·
                refine ⟨6965834437593739221522635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4643889625062492814348423 6965834437593739221522635)
                ·
                  refine ⟨10448751656390608832283953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6965834437593739221522635 10448751656390608832283953)
                  ·
                    refine ⟨7836563742292956624212965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10448751656390608832283953 7836563742292956624212965)
                    ·
                      refine ⟨1469355701679929367039931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7836563742292956624212965 1469355701679929367039931)
                      ·
                        rfl

theorem cell23_2861560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 1, 1, 2, 4].length) (baseStart_2861560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2861560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2861560 prefixEnd_2861560 := by exact prefixLift 2861560
  have htrace : WordTrace (prefixWord ++ tailWord_2861560) baseStart_2861560 baseEnd_2861560 := by
    simpa [prefixWord, tailWord_2861560, baseEnd_2861560] using wordTrace_append hprefix tailTrace_2861560
  have hstable : (prefixWord ++ tailWord_2861560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861560).length < 2 ^ (prefixWord ++ tailWord_2861560).sum := by decide
  have hdescent : baseEnd_2861560 < baseStart_2861560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861581 : List Nat := [1, 7, 1, 1, 1, 2, 1, 3, 1, 1, 4]
def baseStart_2861581 : Nat := 118140960795 + 2861581 * 2 ^ 59
def prefixEnd_2861581 : Nat := 4983230072969 + 3 ^ 40 * 2861581 * 2
def baseEnd_2861581 : Nat := 1469366484773673784877335

theorem tailTrace_2861581 : CollatzResearch.WordTrace tailWord_2861581 prefixEnd_2861581 1469366484773673784877335 := by
  unfold tailWord_2861581
  simp only [CollatzResearch.WordTrace]
  refine ⟨104370433445988230970992597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69580288963992153980661731 104370433445988230970992597)
  ·
    refine ⟨2446182033890349163382639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 104370433445988230970992597 2446182033890349163382639)
    ·
      refine ⟨3669273050835523745073959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2446182033890349163382639 3669273050835523745073959)
      ·
        refine ⟨5503909576253285617610939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3669273050835523745073959 5503909576253285617610939)
        ·
          refine ⟨8255864364379928426416409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5503909576253285617610939 8255864364379928426416409)
          ·
            refine ⟨6191898273284946319812307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8255864364379928426416409 6191898273284946319812307)
            ·
              refine ⟨9287847409927419479718461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6191898273284946319812307 9287847409927419479718461)
              ·
                refine ⟨3482942778722782304894423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9287847409927419479718461 3482942778722782304894423)
                ·
                  refine ⟨5224414168084173457341635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3482942778722782304894423 5224414168084173457341635)
                  ·
                    refine ⟨7836621252126260186012453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5224414168084173457341635 7836621252126260186012453)
                    ·
                      refine ⟨1469366484773673784877335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7836621252126260186012453 1469366484773673784877335)
                      ·
                        rfl

theorem cell23_2861581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_2861581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2861581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2861581 prefixEnd_2861581 := by exact prefixLift 2861581
  have htrace : WordTrace (prefixWord ++ tailWord_2861581) baseStart_2861581 baseEnd_2861581 := by
    simpa [prefixWord, tailWord_2861581, baseEnd_2861581] using wordTrace_append hprefix tailTrace_2861581
  have hstable : (prefixWord ++ tailWord_2861581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861581).length < 2 ^ (prefixWord ++ tailWord_2861581).sum := by decide
  have hdescent : baseEnd_2861581 < baseStart_2861581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861591 : List Nat := [1, 1, 3, 6, 1, 2, 1, 2, 2, 4]
def baseStart_2861591 : Nat := 118140960795 + 2861591 * 2 ^ 59
def prefixEnd_2861591 : Nat := 4983230072969 + 3 ^ 40 * 2861591 * 2
def baseEnd_2861591 : Nat := 489790539860072915250763

theorem tailTrace_2861591 : CollatzResearch.WordTrace tailWord_2861591 prefixEnd_2861591 489790539860072915250763 := by
  unfold tailWord_2861591
  simp only [CollatzResearch.WordTrace]
  refine ⟨104370798175952002678856627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69580532117301335119237751 104370798175952002678856627)
  ·
    refine ⟨156556197263928004018284941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104370798175952002678856627 156556197263928004018284941)
    ·
      refine ⟨58708573973973001506856853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156556197263928004018284941 58708573973973001506856853)
      ·
        refine ⟨2751964405029984445633915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 58708573973973001506856853 2751964405029984445633915)
        ·
          refine ⟨4127946607544976668450873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2751964405029984445633915 4127946607544976668450873)
          ·
            refine ⟨3095959955658732501338155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4127946607544976668450873 3095959955658732501338155)
            ·
              refine ⟨4643939933488098752007233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3095959955658732501338155 4643939933488098752007233)
              ·
                refine ⟨3482954950116074064005425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4643939933488098752007233 3482954950116074064005425)
                ·
                  refine ⟨2612216212587055548004069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3482954950116074064005425 2612216212587055548004069)
                  ·
                    refine ⟨489790539860072915250763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2612216212587055548004069 489790539860072915250763)
                    ·
                      rfl

theorem cell23_2861591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 2, 2, 4].length) (baseStart_2861591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2861591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2861591 prefixEnd_2861591 := by exact prefixLift 2861591
  have htrace : WordTrace (prefixWord ++ tailWord_2861591) baseStart_2861591 baseEnd_2861591 := by
    simpa [prefixWord, tailWord_2861591, baseEnd_2861591] using wordTrace_append hprefix tailTrace_2861591
  have hstable : (prefixWord ++ tailWord_2861591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861591).length < 2 ^ (prefixWord ++ tailWord_2861591).sum := by decide
  have hdescent : baseEnd_2861591 < baseStart_2861591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861593 : List Nat := [1, 2, 1, 2, 1, 1, 2, 4, 2, 2, 5]
def baseStart_2861593 : Nat := 118140960795 + 2861593 * 2 ^ 59
def prefixEnd_2861593 : Nat := 4983230072969 + 3 ^ 40 * 2861593 * 2
def baseEnd_2861593 : Nat := 1469372646541527737927279

theorem tailTrace_2861593 : CollatzResearch.WordTrace tailWord_2861593 prefixEnd_2861593 1469372646541527737927279 := by
  unfold tailWord_2861593
  simp only [CollatzResearch.WordTrace]
  refine ⟨104370871121944757020429433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69580580747963171346952955 104370871121944757020429433)
  ·
    refine ⟨78278153341458567765322075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104370871121944757020429433 78278153341458567765322075)
    ·
      refine ⟨117417230012187851647983113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78278153341458567765322075 117417230012187851647983113)
      ·
        refine ⟨88062922509140888735987335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117417230012187851647983113 88062922509140888735987335)
        ·
          refine ⟨132094383763711333103981003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88062922509140888735987335 132094383763711333103981003)
          ·
            refine ⟨198141575645566999655971505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132094383763711333103981003 198141575645566999655971505)
            ·
              refine ⟨148606181734175249741978629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 198141575645566999655971505 148606181734175249741978629)
              ·
                refine ⟨27863659075157859326620993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 148606181734175249741978629 27863659075157859326620993)
                ·
                  refine ⟨20897744306368394494965745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27863659075157859326620993 20897744306368394494965745)
                  ·
                    refine ⟨15673308229776295871224309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20897744306368394494965745 15673308229776295871224309)
                    ·
                      refine ⟨1469372646541527737927279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15673308229776295871224309 1469372646541527737927279)
                      ·
                        rfl

theorem cell23_2861593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 2, 5].length) (baseStart_2861593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2861593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2861593 prefixEnd_2861593 := by exact prefixLift 2861593
  have htrace : WordTrace (prefixWord ++ tailWord_2861593) baseStart_2861593 baseEnd_2861593 := by
    simpa [prefixWord, tailWord_2861593, baseEnd_2861593] using wordTrace_append hprefix tailTrace_2861593
  have hstable : (prefixWord ++ tailWord_2861593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861593).length < 2 ^ (prefixWord ++ tailWord_2861593).sum := by decide
  have hdescent : baseEnd_2861593 < baseStart_2861593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861624 : List Nat := [2, 1, 2, 1, 4, 1, 4, 2, 1, 3, 2]
def baseStart_2861624 : Nat := 118140960795 + 2861624 * 2 ^ 59
def prefixEnd_2861624 : Nat := 4983230072969 + 3 ^ 40 * 2861624 * 2
def baseEnd_2861624 : Nat := 1469388564441817116639637

theorem tailTrace_2861624 : CollatzResearch.WordTrace tailWord_2861624 prefixEnd_2861624 1469388564441817116639637 := by
  unfold tailWord_2861624
  simp only [CollatzResearch.WordTrace]
  refine ⟨52186000892416224657403963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69581334523221632876538617 52186000892416224657403963)
  ·
    refine ⟨78279001338624336986105945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52186000892416224657403963 78279001338624336986105945)
    ·
      refine ⟨58709251003968252739579459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78279001338624336986105945 58709251003968252739579459)
      ·
        refine ⟨88063876505952379109369189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58709251003968252739579459 88063876505952379109369189)
        ·
          refine ⟨16511976844866071083006723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88063876505952379109369189 16511976844866071083006723)
          ·
            refine ⟨24767965267299106624510085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16511976844866071083006723 24767965267299106624510085)
            ·
              refine ⟨4643993487618582492095641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24767965267299106624510085 4643993487618582492095641)
              ·
                refine ⟨3482995115713936869071731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4643993487618582492095641 3482995115713936869071731)
                ·
                  refine ⟨5224492673570905303607597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3482995115713936869071731 5224492673570905303607597)
                  ·
                    refine ⟨1959184752589089488852849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5224492673570905303607597 1959184752589089488852849)
                    ·
                      refine ⟨1469388564441817116639637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1959184752589089488852849 1469388564441817116639637)
                      ·
                        rfl

theorem cell23_2861624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 2, 1, 3, 2].length) (baseStart_2861624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2861624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2861624 prefixEnd_2861624 := by exact prefixLift 2861624
  have htrace : WordTrace (prefixWord ++ tailWord_2861624) baseStart_2861624 baseEnd_2861624 := by
    simpa [prefixWord, tailWord_2861624, baseEnd_2861624] using wordTrace_append hprefix tailTrace_2861624
  have hstable : (prefixWord ++ tailWord_2861624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861624).length < 2 ^ (prefixWord ++ tailWord_2861624).sum := by decide
  have hdescent : baseEnd_2861624 < baseStart_2861624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861643 : List Nat := [1, 1, 1, 1, 3, 1, 4, 2, 9]
def baseStart_2861643 : Nat := 118140960795 + 2861643 * 2 ^ 59
def prefixEnd_2861643 : Nat := 4983230072969 + 3 ^ 40 * 2861643 * 2
def baseEnd_2861643 : Nat := 163266480063805838033561

theorem tailTrace_2861643 : CollatzResearch.WordTrace tailWord_2861643 prefixEnd_2861643 163266480063805838033561 := by
  unfold tailWord_2861643
  simp only [CollatzResearch.WordTrace]
  refine ⟨104372694771763615559749583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69581796514509077039833055 104372694771763615559749583)
  ·
    refine ⟨156559042157645423339624375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104372694771763615559749583 156559042157645423339624375)
    ·
      refine ⟨234838563236468135009436563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156559042157645423339624375 234838563236468135009436563)
      ·
        refine ⟨352257844854702202514154845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234838563236468135009436563 352257844854702202514154845)
        ·
          refine ⟨132096691820513325942808067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 352257844854702202514154845 132096691820513325942808067)
          ·
            refine ⟨198145037730769988914212101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132096691820513325942808067 198145037730769988914212101)
            ·
              refine ⟨37152194574519372921414769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 198145037730769988914212101 37152194574519372921414769)
              ·
                refine ⟨27864145930889529691061077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37152194574519372921414769 27864145930889529691061077)
                ·
                  refine ⟨163266480063805838033561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 27864145930889529691061077 163266480063805838033561)
                  ·
                    rfl

theorem cell23_2861643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 9].length) (baseStart_2861643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2861643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2861643 prefixEnd_2861643 := by exact prefixLift 2861643
  have htrace : WordTrace (prefixWord ++ tailWord_2861643) baseStart_2861643 baseEnd_2861643 := by
    simpa [prefixWord, tailWord_2861643, baseEnd_2861643] using wordTrace_append hprefix tailTrace_2861643
  have hstable : (prefixWord ++ tailWord_2861643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861643).length < 2 ^ (prefixWord ++ tailWord_2861643).sum := by decide
  have hdescent : baseEnd_2861643 < baseStart_2861643 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861714 : List Nat := [3, 2, 3, 1, 2, 1, 1, 1, 2, 5, 2]
def baseStart_2861714 : Nat := 118140960795 + 2861714 * 2 ^ 59
def prefixEnd_2861714 : Nat := 4983230072969 + 3 ^ 40 * 2861714 * 2
def baseEnd_2861714 : Nat := 1469434777700721764514223

theorem tailTrace_2861714 : CollatzResearch.WordTrace tailWord_2861714 prefixEnd_2861714 1469434777700721764514223 := by
  unfold tailWord_2861714
  simp only [CollatzResearch.WordTrace]
  refine ⟨26093821088626598671396049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69583522903004263123722797 26093821088626598671396049)
  ·
    refine ⟨19570365816469949003547037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26093821088626598671396049 19570365816469949003547037)
    ·
      refine ⟨7338887181176230876330139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19570365816469949003547037 7338887181176230876330139)
      ·
        refine ⟨11008330771764346314495209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7338887181176230876330139 11008330771764346314495209)
        ·
          refine ⟨8256248078823259735871407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11008330771764346314495209 8256248078823259735871407)
          ·
            refine ⟨12384372118234889603807111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8256248078823259735871407 12384372118234889603807111)
            ·
              refine ⟨18576558177352334405710667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12384372118234889603807111 18576558177352334405710667)
              ·
                refine ⟨27864837266028501608566001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18576558177352334405710667 27864837266028501608566001)
                ·
                  refine ⟨20898627949521376206424501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27864837266028501608566001 20898627949521376206424501)
                  ·
                    refine ⟨1959246370267629019352297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20898627949521376206424501 1959246370267629019352297)
                    ·
                      refine ⟨1469434777700721764514223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1959246370267629019352297 1469434777700721764514223)
                      ·
                        rfl

theorem cell23_2861714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 2, 5, 2].length) (baseStart_2861714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2861714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2861714 prefixEnd_2861714 := by exact prefixLift 2861714
  have htrace : WordTrace (prefixWord ++ tailWord_2861714) baseStart_2861714 baseEnd_2861714 := by
    simpa [prefixWord, tailWord_2861714, baseEnd_2861714] using wordTrace_append hprefix tailTrace_2861714
  have hstable : (prefixWord ++ tailWord_2861714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861714).length < 2 ^ (prefixWord ++ tailWord_2861714).sum := by decide
  have hdescent : baseEnd_2861714 < baseStart_2861714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861747 : List Nat := [1, 1, 1, 2, 3, 5, 1, 1, 1, 4, 3]
def baseStart_2861747 : Nat := 118140960795 + 2861747 * 2 ^ 59
def prefixEnd_2861747 : Nat := 4983230072969 + 3 ^ 40 * 2861747 * 2
def baseEnd_2861747 : Nat := 1469451722562320135401571

theorem tailTrace_2861747 : CollatzResearch.WordTrace tailWord_2861747 prefixEnd_2861747 1469451722562320135401571 := by
  unfold tailWord_2861747
  simp only [CollatzResearch.WordTrace]
  refine ⟨104376487963386841321535495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69584325308924560881023663 104376487963386841321535495)
  ·
    refine ⟨156564731945080261982303243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104376487963386841321535495 156564731945080261982303243)
    ·
      refine ⟨234847097917620392973454865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156564731945080261982303243 234847097917620392973454865)
      ·
        refine ⟨176135323438215294730091149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234847097917620392973454865 176135323438215294730091149)
        ·
          refine ⟨66050746289330735523784181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176135323438215294730091149 66050746289330735523784181)
          ·
            refine ⟨6192257464624756455354767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 66050746289330735523784181 6192257464624756455354767)
            ·
              refine ⟨9288386196937134683032151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6192257464624756455354767 9288386196937134683032151)
              ·
                refine ⟨13932579295405702024548227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9288386196937134683032151 13932579295405702024548227)
                ·
                  refine ⟨20898868943108553036822341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13932579295405702024548227 20898868943108553036822341)
                  ·
                    refine ⟨3918537926832853694404189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20898868943108553036822341 3918537926832853694404189)
                    ·
                      refine ⟨1469451722562320135401571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3918537926832853694404189 1469451722562320135401571)
                      ·
                        rfl

theorem cell23_2861747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 4, 3].length) (baseStart_2861747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2861747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2861747 prefixEnd_2861747 := by exact prefixLift 2861747
  have htrace : WordTrace (prefixWord ++ tailWord_2861747) baseStart_2861747 baseEnd_2861747 := by
    simpa [prefixWord, tailWord_2861747, baseEnd_2861747] using wordTrace_append hprefix tailTrace_2861747
  have hstable : (prefixWord ++ tailWord_2861747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861747).length < 2 ^ (prefixWord ++ tailWord_2861747).sum := by decide
  have hdescent : baseEnd_2861747 < baseStart_2861747 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861784 : List Nat := [2, 1, 2, 2, 3, 3, 3, 1, 6]
def baseStart_2861784 : Nat := 118140960795 + 2861784 * 2 ^ 59
def prefixEnd_2861784 : Nat := 4983230072969 + 3 ^ 40 * 2861784 * 2
def baseEnd_2861784 : Nat := 163274524594059610070989

theorem tailTrace_2861784 : CollatzResearch.WordTrace tailWord_2861784 prefixEnd_2861784 163274524594059610070989 := by
  unfold tailWord_2861784
  simp only [CollatzResearch.WordTrace]
  refine ⟨52188918732126398320316203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69585224976168531093754937 52188918732126398320316203)
  ·
    refine ⟨78283378098189597480474305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52188918732126398320316203 78283378098189597480474305)
    ·
      refine ⟨58712533573642198110355729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78283378098189597480474305 58712533573642198110355729)
      ·
        refine ⟨44034400180231648582766797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58712533573642198110355729 44034400180231648582766797)
        ·
          refine ⟨16512900067586868218537549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44034400180231648582766797 16512900067586868218537549)
          ·
            refine ⟨6192337525345075581951581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16512900067586868218537549 6192337525345075581951581)
            ·
              refine ⟨2322126572004403343231843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6192337525345075581951581 2322126572004403343231843)
              ·
                refine ⟨3483189858006605014847765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2322126572004403343231843 3483189858006605014847765)
                ·
                  refine ⟨163274524594059610070989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3483189858006605014847765 163274524594059610070989)
                  ·
                    rfl

theorem cell23_2861784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 3, 1, 6].length) (baseStart_2861784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2861784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2861784 prefixEnd_2861784 := by exact prefixLift 2861784
  have htrace : WordTrace (prefixWord ++ tailWord_2861784) baseStart_2861784 baseEnd_2861784 := by
    simpa [prefixWord, tailWord_2861784, baseEnd_2861784] using wordTrace_append hprefix tailTrace_2861784
  have hstable : (prefixWord ++ tailWord_2861784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861784).length < 2 ^ (prefixWord ++ tailWord_2861784).sum := by decide
  have hdescent : baseEnd_2861784 < baseStart_2861784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861804 : List Nat := [2, 2, 1, 1, 2, 2, 1, 5, 2, 3, 2]
def baseStart_2861804 : Nat := 118140960795 + 2861804 * 2 ^ 59
def prefixEnd_2861804 : Nat := 4983230072969 + 3 ^ 40 * 2861804 * 2
def baseEnd_2861804 : Nat := 1469480990959626412388809

theorem tailTrace_2861804 : CollatzResearch.WordTrace tailWord_2861804 prefixEnd_2861804 1469480990959626412388809 := by
  unfold tailWord_2861804
  simp only [CollatzResearch.WordTrace]
  refine ⟨52189283462090170028180233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69585711282786893370906977 52189283462090170028180233)
  ·
    refine ⟨39141962596567627521135175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52189283462090170028180233 39141962596567627521135175)
    ·
      refine ⟨58712943894851441281702763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39141962596567627521135175 58712943894851441281702763)
      ·
        refine ⟨88069415842277161922554145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58712943894851441281702763 88069415842277161922554145)
        ·
          refine ⟨66052061881707871441915609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88069415842277161922554145 66052061881707871441915609)
          ·
            refine ⟨49539046411280903581436707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66052061881707871441915609 49539046411280903581436707)
            ·
              refine ⟨74308569616921355372155061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49539046411280903581436707 74308569616921355372155061)
              ·
                refine ⟨6966428401586377066139537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74308569616921355372155061 6966428401586377066139537)
                ·
                  refine ⟨5224821301189782799604653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6966428401586377066139537 5224821301189782799604653)
                  ·
                    refine ⟨1959307987946168549851745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5224821301189782799604653 1959307987946168549851745)
                    ·
                      refine ⟨1469480990959626412388809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1959307987946168549851745 1469480990959626412388809)
                      ·
                        rfl

theorem cell23_2861804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 3, 2].length) (baseStart_2861804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2861804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2861804 prefixEnd_2861804 := by exact prefixLift 2861804
  have htrace : WordTrace (prefixWord ++ tailWord_2861804) baseStart_2861804 baseEnd_2861804 := by
    simpa [prefixWord, tailWord_2861804, baseEnd_2861804] using wordTrace_append hprefix tailTrace_2861804
  have hstable : (prefixWord ++ tailWord_2861804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861804).length < 2 ^ (prefixWord ++ tailWord_2861804).sum := by decide
  have hdescent : baseEnd_2861804 < baseStart_2861804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861814 : List Nat := [5, 1, 1, 1, 1, 2, 1, 5, 1, 5]
def baseStart_2861814 : Nat := 118140960795 + 2861814 * 2 ^ 59
def prefixEnd_2861814 : Nat := 4983230072969 + 3 ^ 40 * 2861814 * 2
def baseEnd_2861814 : Nat := 489828708588723791087921

theorem tailTrace_2861814 : CollatzResearch.WordTrace tailWord_2861814 prefixEnd_2861814 489828708588723791087921 := by
  unfold tailWord_2861814
  simp only [CollatzResearch.WordTrace]
  refine ⟨6523683228384006985264031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69585954436096074509482997 6523683228384006985264031)
  ·
    refine ⟨9785524842576010477896047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6523683228384006985264031 9785524842576010477896047)
    ·
      refine ⟨14678287263864015716844071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9785524842576010477896047 14678287263864015716844071)
      ·
        refine ⟨22017430895796023575266107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14678287263864015716844071 22017430895796023575266107)
        ·
          refine ⟨33026146343694035362899161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22017430895796023575266107 33026146343694035362899161)
          ·
            refine ⟨24769609757770526522174371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33026146343694035362899161 24769609757770526522174371)
            ·
              refine ⟨37154414636655789783261557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24769609757770526522174371 37154414636655789783261557)
              ·
                refine ⟨3483226372186480292180771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37154414636655789783261557 3483226372186480292180771)
                ·
                  refine ⟨5224839558279720438271157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3483226372186480292180771 5224839558279720438271157)
                  ·
                    refine ⟨489828708588723791087921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5224839558279720438271157 489828708588723791087921)
                    ·
                      rfl

theorem cell23_2861814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 5, 1, 5].length) (baseStart_2861814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2861814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2861814 prefixEnd_2861814 := by exact prefixLift 2861814
  have htrace : WordTrace (prefixWord ++ tailWord_2861814) baseStart_2861814 baseEnd_2861814 := by
    simpa [prefixWord, tailWord_2861814, baseEnd_2861814] using wordTrace_append hprefix tailTrace_2861814
  have hstable : (prefixWord ++ tailWord_2861814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861814).length < 2 ^ (prefixWord ++ tailWord_2861814).sum := by decide
  have hdescent : baseEnd_2861814 < baseStart_2861814 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861864 : List Nat := [2, 1, 5, 1, 1, 1, 3, 2, 1, 2, 4]
def baseStart_2861864 : Nat := 118140960795 + 2861864 * 2 ^ 59
def prefixEnd_2861864 : Nat := 4983230072969 + 3 ^ 40 * 2861864 * 2
def baseEnd_2861864 : Nat := 1469511799798896177638533

theorem tailTrace_2861864 : CollatzResearch.WordTrace tailWord_2861864 prefixEnd_2861864 1469511799798896177638533 := by
  unfold tailWord_2861864
  simp only [CollatzResearch.WordTrace]
  refine ⟨52190377651981485151772323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69587170202641980202363097 52190377651981485151772323)
  ·
    refine ⟨78285566477972227727658485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52190377651981485151772323 78285566477972227727658485)
    ·
      refine ⟨7339271857309896349467983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 78285566477972227727658485 7339271857309896349467983)
      ·
        refine ⟨11008907785964844524201975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7339271857309896349467983 11008907785964844524201975)
        ·
          refine ⟨16513361678947266786302963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11008907785964844524201975 16513361678947266786302963)
          ·
            refine ⟨24770042518420900179454445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16513361678947266786302963 24770042518420900179454445)
            ·
              refine ⟨9288765944407837567295417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24770042518420900179454445 9288765944407837567295417)
              ·
                refine ⟨6966574458305878175471563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9288765944407837567295417 6966574458305878175471563)
                ·
                  refine ⟨10449861687458817263207345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6966574458305878175471563 10449861687458817263207345)
                  ·
                    refine ⟨7837396265594112947405509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10449861687458817263207345 7837396265594112947405509)
                    ·
                      refine ⟨1469511799798896177638533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7837396265594112947405509 1469511799798896177638533)
                      ·
                        rfl

theorem cell23_2861864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_2861864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2861864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2861864 prefixEnd_2861864 := by exact prefixLift 2861864
  have htrace : WordTrace (prefixWord ++ tailWord_2861864) baseStart_2861864 baseEnd_2861864 := by
    simpa [prefixWord, tailWord_2861864, baseEnd_2861864] using wordTrace_append hprefix tailTrace_2861864
  have hstable : (prefixWord ++ tailWord_2861864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861864).length < 2 ^ (prefixWord ++ tailWord_2861864).sum := by decide
  have hdescent : baseEnd_2861864 < baseStart_2861864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861867 : List Nat := [1, 1, 1, 1, 2, 1, 2, 5, 3, 3, 3]
def baseStart_2861867 : Nat := 118140960795 + 2861867 * 2 ^ 59
def prefixEnd_2861867 : Nat := 4983230072969 + 3 ^ 40 * 2861867 * 2
def baseEnd_2861867 : Nat := 1469513340240859665901019

theorem tailTrace_2861867 : CollatzResearch.WordTrace tailWord_2861867 prefixEnd_2861867 1469513340240859665901019 := by
  unfold tailWord_2861867
  simp only [CollatzResearch.WordTrace]
  refine ⟨104380864722952101815903855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69587243148634734543935903 104380864722952101815903855)
  ·
    refine ⟨156571297084428152723855783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104380864722952101815903855 156571297084428152723855783)
    ·
      refine ⟨234856945626642229085783675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156571297084428152723855783 234856945626642229085783675)
      ·
        refine ⟨352285418439963343628675513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234856945626642229085783675 352285418439963343628675513)
        ·
          refine ⟨264214063829972507721506635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 352285418439963343628675513 264214063829972507721506635)
          ·
            refine ⟨396321095744958761582259953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264214063829972507721506635 396321095744958761582259953)
            ·
              refine ⟨297240821808719071186694965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 396321095744958761582259953 297240821808719071186694965)
              ·
                refine ⟨27866327044567412923752653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 297240821808719071186694965 27866327044567412923752653)
                ·
                  refine ⟨10449872641712779846407245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27866327044567412923752653 10449872641712779846407245)
                  ·
                    refine ⟨3918702240642292442402717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10449872641712779846407245 3918702240642292442402717)
                    ·
                      refine ⟨1469513340240859665901019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3918702240642292442402717 1469513340240859665901019)
                      ·
                        rfl

theorem cell23_2861867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 3, 3, 3].length) (baseStart_2861867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2861867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2861867 prefixEnd_2861867 := by exact prefixLift 2861867
  have htrace : WordTrace (prefixWord ++ tailWord_2861867) baseStart_2861867 baseEnd_2861867 := by
    simpa [prefixWord, tailWord_2861867, baseEnd_2861867] using wordTrace_append hprefix tailTrace_2861867
  have hstable : (prefixWord ++ tailWord_2861867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861867).length < 2 ^ (prefixWord ++ tailWord_2861867).sum := by decide
  have hdescent : baseEnd_2861867 < baseStart_2861867 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861868 : List Nat := [2, 2, 1, 1, 1, 4, 2, 5, 1, 2, 2]
def baseStart_2861868 : Nat := 118140960795 + 2861868 * 2 ^ 59
def prefixEnd_2861868 : Nat := 4983230072969 + 3 ^ 40 * 2861868 * 2
def baseEnd_2861868 : Nat := 1469513853721514161988515

theorem tailTrace_2861868 : CollatzResearch.WordTrace tailWord_2861868 prefixEnd_2861868 1469513853721514161988515 := by
  unfold tailWord_2861868
  simp only [CollatzResearch.WordTrace]
  refine ⟨52190450597974239493345129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69587267463965652657793505 52190450597974239493345129)
  ·
    refine ⟨39142837948480679620008847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52190450597974239493345129 39142837948480679620008847)
    ·
      refine ⟨58714256922721019430013271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39142837948480679620008847 58714256922721019430013271)
      ·
        refine ⟨88071385384081529145019907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58714256922721019430013271 88071385384081529145019907)
        ·
          refine ⟨132107078076122293717529861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88071385384081529145019907 132107078076122293717529861)
          ·
            refine ⟨24770077139272930072036849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 132107078076122293717529861 24770077139272930072036849)
            ·
              refine ⟨18577557854454697554027637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24770077139272930072036849 18577557854454697554027637)
              ·
                refine ⟨1741646048855127895690091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18577557854454697554027637 1741646048855127895690091)
                ·
                  refine ⟨2612469073282691843535137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1741646048855127895690091 2612469073282691843535137)
                  ·
                    refine ⟨1959351804962018882651353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2612469073282691843535137 1959351804962018882651353)
                    ·
                      refine ⟨1469513853721514161988515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1959351804962018882651353 1469513853721514161988515)
                      ·
                        rfl

theorem cell23_2861868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 5, 1, 2, 2].length) (baseStart_2861868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2861868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2861868 prefixEnd_2861868 := by exact prefixLift 2861868
  have htrace : WordTrace (prefixWord ++ tailWord_2861868) baseStart_2861868 baseEnd_2861868 := by
    simpa [prefixWord, tailWord_2861868, baseEnd_2861868] using wordTrace_append hprefix tailTrace_2861868
  have hstable : (prefixWord ++ tailWord_2861868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861868).length < 2 ^ (prefixWord ++ tailWord_2861868).sum := by decide
  have hdescent : baseEnd_2861868 < baseStart_2861868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861887 : List Nat := [1, 1, 2, 2, 5, 1, 1, 1, 2, 7]
def baseStart_2861887 : Nat := 118140960795 + 2861887 * 2 ^ 59
def prefixEnd_2861887 : Nat := 4983230072969 + 3 ^ 40 * 2861887 * 2
def baseEnd_2861887 : Nat := 489841203284649862550309

theorem tailTrace_2861887 : CollatzResearch.WordTrace tailWord_2861887 prefixEnd_2861887 489841203284649862550309 := by
  unfold tailWord_2861887
  simp only [CollatzResearch.WordTrace]
  refine ⟨104381594182879645231631915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69587729455253096821087943 104381594182879645231631915)
  ·
    refine ⟨156572391274319467847447873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104381594182879645231631915 156572391274319467847447873)
    ·
      refine ⟨117429293455739600885585905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156572391274319467847447873 117429293455739600885585905)
      ·
        refine ⟨88071970091804700664189429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117429293455739600885585905 88071970091804700664189429)
        ·
          refine ⟨8256747196106690687267759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 88071970091804700664189429 8256747196106690687267759)
          ·
            refine ⟨12385120794160036030901639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8256747196106690687267759 12385120794160036030901639)
            ·
              refine ⟨18577681191240054046352459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12385120794160036030901639 18577681191240054046352459)
              ·
                refine ⟨27866521786860081069528689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18577681191240054046352459 27866521786860081069528689)
                ·
                  refine ⟨20899891340145060802146517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27866521786860081069528689 20899891340145060802146517)
                  ·
                    refine ⟨489841203284649862550309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20899891340145060802146517 489841203284649862550309)
                    ·
                      rfl

theorem cell23_2861887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 7].length) (baseStart_2861887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2861887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2861887 prefixEnd_2861887 := by exact prefixLift 2861887
  have htrace : WordTrace (prefixWord ++ tailWord_2861887) baseStart_2861887 baseEnd_2861887 := by
    simpa [prefixWord, tailWord_2861887, baseEnd_2861887] using wordTrace_append hprefix tailTrace_2861887
  have hstable : (prefixWord ++ tailWord_2861887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861887).length < 2 ^ (prefixWord ++ tailWord_2861887).sum := by decide
  have hdescent : baseEnd_2861887 < baseStart_2861887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861911 : List Nat := [1, 1, 3, 2, 4, 1, 2, 1, 3, 3, 2]
def baseStart_2861911 : Nat := 118140960795 + 2861911 * 2 ^ 59
def prefixEnd_2861911 : Nat := 4983230072969 + 3 ^ 40 * 2861911 * 2
def baseEnd_2861911 : Nat := 1469535933389657493750817

theorem tailTrace_2861911 : CollatzResearch.WordTrace tailWord_2861911 prefixEnd_2861911 1469535933389657493750817 := by
  unfold tailWord_2861911
  simp only [CollatzResearch.WordTrace]
  refine ⟨104382469534792697330505587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69588313023195131553670391 104382469534792697330505587)
  ·
    refine ⟨156573704302189045995758381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104382469534792697330505587 156573704302189045995758381)
    ·
      refine ⟨58715139113320892248409393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156573704302189045995758381 58715139113320892248409393)
      ·
        refine ⟨44036354334990669186307045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58715139113320892248409393 44036354334990669186307045)
        ·
          refine ⟨8256816437810750472432571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44036354334990669186307045 8256816437810750472432571)
          ·
            refine ⟨12385224656716125708648857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8256816437810750472432571 12385224656716125708648857)
            ·
              refine ⟨9288918492537094281486643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12385224656716125708648857 9288918492537094281486643)
              ·
                refine ⟨13933377738805641422229965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9288918492537094281486643 13933377738805641422229965)
                ·
                  refine ⟨5225016652052115533336237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13933377738805641422229965 5225016652052115533336237)
                  ·
                    refine ⟨1959381244519543325001089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5225016652052115533336237 1959381244519543325001089)
                    ·
                      refine ⟨1469535933389657493750817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1959381244519543325001089 1469535933389657493750817)
                      ·
                        rfl

theorem cell23_2861911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 3, 3, 2].length) (baseStart_2861911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2861911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2861911 prefixEnd_2861911 := by exact prefixLift 2861911
  have htrace : WordTrace (prefixWord ++ tailWord_2861911) baseStart_2861911 baseEnd_2861911 := by
    simpa [prefixWord, tailWord_2861911, baseEnd_2861911] using wordTrace_append hprefix tailTrace_2861911
  have hstable : (prefixWord ++ tailWord_2861911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861911).length < 2 ^ (prefixWord ++ tailWord_2861911).sum := by decide
  have hdescent : baseEnd_2861911 < baseStart_2861911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861922 : List Nat := [3, 3, 2, 1, 4, 1, 2, 1, 1, 2, 3]
def baseStart_2861922 : Nat := 118140960795 + 2861922 * 2 ^ 59
def prefixEnd_2861922 : Nat := 4983230072969 + 3 ^ 40 * 2861922 * 2
def baseEnd_2861922 : Nat := 1469541581676856950713267

theorem tailTrace_2861922 : CollatzResearch.WordTrace tailWord_2861922 prefixEnd_2861922 1469541581676856950713267 := by
  unfold tailWord_2861922
  simp only [CollatzResearch.WordTrace]
  refine ⟨26095717684438211552289005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69588580491835230806104013 26095717684438211552289005)
  ·
    refine ⟨9785894131664329332108377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26095717684438211552289005 9785894131664329332108377)
    ·
      refine ⟨7339420598748246999081283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9785894131664329332108377 7339420598748246999081283)
      ·
        refine ⟨11009130898122370498621925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7339420598748246999081283 11009130898122370498621925)
        ·
          refine ⟨2064212043397944468491611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11009130898122370498621925 2064212043397944468491611)
          ·
            refine ⟨3096318065096916702737417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2064212043397944468491611 3096318065096916702737417)
            ·
              refine ⟨2322238548822687527053063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3096318065096916702737417 2322238548822687527053063)
              ·
                refine ⟨3483357823234031290579595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2322238548822687527053063 3483357823234031290579595)
                ·
                  refine ⟨5225036734851046935869393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3483357823234031290579595 5225036734851046935869393)
                  ·
                    refine ⟨3918777551138285201902045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5225036734851046935869393 3918777551138285201902045)
                    ·
                      refine ⟨1469541581676856950713267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3918777551138285201902045 1469541581676856950713267)
                      ·
                        rfl

theorem cell23_2861922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 2, 1, 1, 2, 3].length) (baseStart_2861922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2861922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2861922 prefixEnd_2861922 := by exact prefixLift 2861922
  have htrace : WordTrace (prefixWord ++ tailWord_2861922) baseStart_2861922 baseEnd_2861922 := by
    simpa [prefixWord, tailWord_2861922, baseEnd_2861922] using wordTrace_append hprefix tailTrace_2861922
  have hstable : (prefixWord ++ tailWord_2861922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861922).length < 2 ^ (prefixWord ++ tailWord_2861922).sum := by decide
  have hdescent : baseEnd_2861922 < baseStart_2861922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861928 : List Nat := [2, 1, 4, 2, 1, 3, 1, 3, 1, 3, 2]
def baseStart_2861928 : Nat := 118140960795 + 2861928 * 2 ^ 59
def prefixEnd_2861928 : Nat := 4983230072969 + 3 ^ 40 * 2861928 * 2
def baseEnd_2861928 : Nat := 1469544662560783927238239

theorem tailTrace_2861928 : CollatzResearch.WordTrace tailWord_2861928 prefixEnd_2861928 1469544662560783927238239 := by
  unfold tailWord_2861928
  simp only [CollatzResearch.WordTrace]
  refine ⟨52191544787865554616937219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69588726383820739489249625 52191544787865554616937219)
  ·
    refine ⟨78287317181798331925405829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52191544787865554616937219 78287317181798331925405829)
    ·
      refine ⟨14678871971587187236013593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78287317181798331925405829 14678871971587187236013593)
      ·
        refine ⟨11009153978690390427010195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14678871971587187236013593 11009153978690390427010195)
        ·
          refine ⟨16513730968035585640515293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11009153978690390427010195 16513730968035585640515293)
          ·
            refine ⟨6192649113013344615193235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16513730968035585640515293 6192649113013344615193235)
            ·
              refine ⟨9288973669520016922789853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6192649113013344615193235 9288973669520016922789853)
              ·
                refine ⟨3483365126070006346046195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9288973669520016922789853 3483365126070006346046195)
                ·
                  refine ⟨5225047689105009519069293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3483365126070006346046195 5225047689105009519069293)
                  ·
                    refine ⟨1959392883414378569650985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5225047689105009519069293 1959392883414378569650985)
                    ·
                      refine ⟨1469544662560783927238239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1959392883414378569650985 1469544662560783927238239)
                      ·
                        rfl

theorem cell23_2861928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 3, 1, 3, 2].length) (baseStart_2861928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2861928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2861928 prefixEnd_2861928 := by exact prefixLift 2861928
  have htrace : WordTrace (prefixWord ++ tailWord_2861928) baseStart_2861928 baseEnd_2861928 := by
    simpa [prefixWord, tailWord_2861928, baseEnd_2861928] using wordTrace_append hprefix tailTrace_2861928
  have hstable : (prefixWord ++ tailWord_2861928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861928).length < 2 ^ (prefixWord ++ tailWord_2861928).sum := by decide
  have hdescent : baseEnd_2861928 < baseStart_2861928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2861947 : List Nat := [1, 1, 1, 1, 1, 5, 3, 3, 7]
def baseStart_2861947 : Nat := 118140960795 + 2861947 * 2 ^ 59
def prefixEnd_2861947 : Nat := 4983230072969 + 3 ^ 40 * 2861947 * 2
def baseEnd_2861947 : Nat := 163283824299246594766739

theorem tailTrace_2861947 : CollatzResearch.WordTrace tailWord_2861947 prefixEnd_2861947 163283824299246594766739 := by
  unfold tailWord_2861947
  simp only [CollatzResearch.WordTrace]
  refine ⟨104383782562662275478816095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69589188375108183652544063 104383782562662275478816095)
  ·
    refine ⟨156575673843993413218224143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104383782562662275478816095 156575673843993413218224143)
    ·
      refine ⟨234863510765990119827336215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156575673843993413218224143 234863510765990119827336215)
      ·
        refine ⟨352295266148985179741004323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234863510765990119827336215 352295266148985179741004323)
        ·
          refine ⟨528442899223477769611506485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 352295266148985179741004323 528442899223477769611506485)
          ·
            refine ⟨49541521802201040901078733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 528442899223477769611506485 49541521802201040901078733)
            ·
              refine ⟨18578070675825390337904525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49541521802201040901078733 18578070675825390337904525)
              ·
                refine ⟨6966776503434521376714197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18578070675825390337904525 6966776503434521376714197)
                ·
                  refine ⟨163283824299246594766739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6966776503434521376714197 163283824299246594766739)
                  ·
                    rfl

theorem cell23_2861947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 3, 7].length) (baseStart_2861947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2861947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2861947 prefixEnd_2861947 := by exact prefixLift 2861947
  have htrace : WordTrace (prefixWord ++ tailWord_2861947) baseStart_2861947 baseEnd_2861947 := by
    simpa [prefixWord, tailWord_2861947, baseEnd_2861947] using wordTrace_append hprefix tailTrace_2861947
  have hstable : (prefixWord ++ tailWord_2861947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2861947).length < 2 ^ (prefixWord ++ tailWord_2861947).sum := by decide
  have hdescent : baseEnd_2861947 < baseStart_2861947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2861947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862031 : List Nat := [1, 1, 2, 1, 1, 7, 2, 1, 2, 1, 4]
def baseStart_2862031 : Nat := 118140960795 + 2862031 * 2 ^ 59
def prefixEnd_2862031 : Nat := 4983230072969 + 3 ^ 40 * 2862031 * 2
def baseEnd_2862031 : Nat := 1469597551068197024250265

theorem tailTrace_2862031 : CollatzResearch.WordTrace tailWord_2862031 prefixEnd_2862031 1469597551068197024250265 := by
  unfold tailWord_2862031
  simp only [CollatzResearch.WordTrace]
  refine ⟨104386846294357957824873947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69591230862905305216582631 104386846294357957824873947)
  ·
    refine ⟨156580269441536936737310921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104386846294357957824873947 156580269441536936737310921)
    ·
      refine ⟨117435202081152702552983191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156580269441536936737310921 117435202081152702552983191)
      ·
        refine ⟨176152803121729053829474787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117435202081152702552983191 176152803121729053829474787)
        ·
          refine ⟨264229204682593580744212181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176152803121729053829474787 264229204682593580744212181)
          ·
            refine ⟨6192871984748287048692473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 264229204682593580744212181 6192871984748287048692473)
            ·
              refine ⟨4644653988561215286519355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6192871984748287048692473 4644653988561215286519355)
              ·
                refine ⟨6966980982841822929779033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4644653988561215286519355 6966980982841822929779033)
                ·
                  refine ⟨5225235737131367197334275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6966980982841822929779033 5225235737131367197334275)
                  ·
                    refine ⟨7837853605697050796001413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5225235737131367197334275 7837853605697050796001413)
                    ·
                      refine ⟨1469597551068197024250265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7837853605697050796001413 1469597551068197024250265)
                      ·
                        rfl

theorem cell23_2862031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 1, 2, 1, 4].length) (baseStart_2862031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2862031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2862031 prefixEnd_2862031 := by exact prefixLift 2862031
  have htrace : WordTrace (prefixWord ++ tailWord_2862031) baseStart_2862031 baseEnd_2862031 := by
    simpa [prefixWord, tailWord_2862031, baseEnd_2862031] using wordTrace_append hprefix tailTrace_2862031
  have hstable : (prefixWord ++ tailWord_2862031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862031).length < 2 ^ (prefixWord ++ tailWord_2862031).sum := by decide
  have hdescent : baseEnd_2862031 < baseStart_2862031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862051 : List Nat := [1, 1, 1, 6, 1, 1, 1, 4, 2, 2, 3]
def baseStart_2862051 : Nat := 118140960795 + 2862051 * 2 ^ 59
def prefixEnd_2862051 : Nat := 4983230072969 + 3 ^ 40 * 2862051 * 2
def baseEnd_2862051 : Nat := 1469607820681286946000173

theorem tailTrace_2862051 : CollatzResearch.WordTrace tailWord_2862051 prefixEnd_2862051 1469607820681286946000173 := by
  unfold tailWord_2862051
  simp only [CollatzResearch.WordTrace]
  refine ⟨104387575754285501240602007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69591717169523667493734671 104387575754285501240602007)
  ·
    refine ⟨156581363631428251860903011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104387575754285501240602007 156581363631428251860903011)
    ·
      refine ⟨234872045447142377791354517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156581363631428251860903011 234872045447142377791354517)
      ·
        refine ⟨11009627130334798958969743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 234872045447142377791354517 11009627130334798958969743)
        ·
          refine ⟨16514440695502198438454615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11009627130334798958969743 16514440695502198438454615)
          ·
            refine ⟨24771661043253297657681923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16514440695502198438454615 24771661043253297657681923)
            ·
              refine ⟨37157491564879946486522885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24771661043253297657681923 37157491564879946486522885)
              ·
                refine ⟨6967029668414989966223041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37157491564879946486522885 6967029668414989966223041)
                ·
                  refine ⟨5225272251311242474667281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6967029668414989966223041 5225272251311242474667281)
                  ·
                    refine ⟨3918954188483431856000461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5225272251311242474667281 3918954188483431856000461)
                    ·
                      refine ⟨1469607820681286946000173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3918954188483431856000461 1469607820681286946000173)
                      ·
                        rfl

theorem cell23_2862051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_2862051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2862051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2862051 prefixEnd_2862051 := by exact prefixLift 2862051
  have htrace : WordTrace (prefixWord ++ tailWord_2862051) baseStart_2862051 baseEnd_2862051 := by
    simpa [prefixWord, tailWord_2862051, baseEnd_2862051] using wordTrace_append hprefix tailTrace_2862051
  have hstable : (prefixWord ++ tailWord_2862051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862051).length < 2 ^ (prefixWord ++ tailWord_2862051).sum := by decide
  have hdescent : baseEnd_2862051 < baseStart_2862051 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862064 : List Nat := [2, 1, 1, 1, 3, 2, 1, 2, 2, 5, 3]
def baseStart_2862064 : Nat := 118140960795 + 2862064 * 2 ^ 59
def prefixEnd_2862064 : Nat := 4983230072969 + 3 ^ 40 * 2862064 * 2
def baseEnd_2862064 : Nat := 1469614495929795395137613

theorem tailTrace_2862064 : CollatzResearch.WordTrace tailWord_2862064 prefixEnd_2862064 1469614495929795395137613 := by
  unfold tailWord_2862064
  simp only [CollatzResearch.WordTrace]
  refine ⟨52194024951619202230412623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69592033268825602973883497 52194024951619202230412623)
  ·
    refine ⟨78291037427428803345618935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52194024951619202230412623 78291037427428803345618935)
    ·
      refine ⟨117436556141143205018428403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78291037427428803345618935 117436556141143205018428403)
      ·
        refine ⟨176154834211714807527642605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117436556141143205018428403 176154834211714807527642605)
        ·
          refine ⟨66058062829393052822865977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176154834211714807527642605 66058062829393052822865977)
          ·
            refine ⟨49543547122044789617149483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66058062829393052822865977 49543547122044789617149483)
            ·
              refine ⟨74315320683067184425724225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49543547122044789617149483 74315320683067184425724225)
              ·
                refine ⟨55736490512300388319293169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74315320683067184425724225 55736490512300388319293169)
                ·
                  refine ⟨41802367884225291239469877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55736490512300388319293169 41802367884225291239469877)
                  ·
                    refine ⟨3918971989146121053700301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41802367884225291239469877 3918971989146121053700301)
                    ·
                      refine ⟨1469614495929795395137613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3918971989146121053700301 1469614495929795395137613)
                      ·
                        rfl

theorem cell23_2862064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 2, 5, 3].length) (baseStart_2862064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2862064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2862064 prefixEnd_2862064 := by exact prefixLift 2862064
  have htrace : WordTrace (prefixWord ++ tailWord_2862064) baseStart_2862064 baseEnd_2862064 := by
    simpa [prefixWord, tailWord_2862064, baseEnd_2862064] using wordTrace_append hprefix tailTrace_2862064
  have hstable : (prefixWord ++ tailWord_2862064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862064).length < 2 ^ (prefixWord ++ tailWord_2862064).sum := by decide
  have hdescent : baseEnd_2862064 < baseStart_2862064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862082 : List Nat := [3, 4, 1, 3, 1, 2, 1, 1, 2, 1, 4]
def baseStart_2862082 : Nat := 118140960795 + 2862082 * 2 ^ 59
def prefixEnd_2862082 : Nat := 4983230072969 + 3 ^ 40 * 2862082 * 2
def baseEnd_2862082 : Nat := 1469623738581576324712531

theorem tailTrace_2862082 : CollatzResearch.WordTrace tailWord_2862082 prefixEnd_2862082 1469623738581576324712531 := by
  unfold tailWord_2862082
  simp only [CollatzResearch.WordTrace]
  refine ⟨26097176604293298383745125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69592470944782129023320333 26097176604293298383745125)
  ·
    refine ⟨4893220613304993446952211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26097176604293298383745125 4893220613304993446952211)
    ·
      refine ⟨7339830919957490170428317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4893220613304993446952211 7339830919957490170428317)
      ·
        refine ⟨2752436594984058813910619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7339830919957490170428317 2752436594984058813910619)
        ·
          refine ⟨4128654892476088220865929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2752436594984058813910619 4128654892476088220865929)
          ·
            refine ⟨3096491169357066165649447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4128654892476088220865929 3096491169357066165649447)
            ·
              refine ⟨4644736754035599248474171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3096491169357066165649447 4644736754035599248474171)
              ·
                refine ⟨6967105131053398872711257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4644736754035599248474171 6967105131053398872711257)
                ·
                  refine ⟨5225328848290049154533443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6967105131053398872711257 5225328848290049154533443)
                  ·
                    refine ⟨7837993272435073731800165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5225328848290049154533443 7837993272435073731800165)
                    ·
                      refine ⟨1469623738581576324712531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7837993272435073731800165 1469623738581576324712531)
                      ·
                        rfl

theorem cell23_2862082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_2862082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2862082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2862082 prefixEnd_2862082 := by exact prefixLift 2862082
  have htrace : WordTrace (prefixWord ++ tailWord_2862082) baseStart_2862082 baseEnd_2862082 := by
    simpa [prefixWord, tailWord_2862082, baseEnd_2862082] using wordTrace_append hprefix tailTrace_2862082
  have hstable : (prefixWord ++ tailWord_2862082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862082).length < 2 ^ (prefixWord ++ tailWord_2862082).sum := by decide
  have hdescent : baseEnd_2862082 < baseStart_2862082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862115 : List Nat := [1, 1, 1, 4, 3, 2, 2, 4, 1, 1, 3]
def baseStart_2862115 : Nat := 118140960795 + 2862115 * 2 ^ 59
def prefixEnd_2862115 : Nat := 4983230072969 + 3 ^ 40 * 2862115 * 2
def baseEnd_2862115 : Nat := 1469640683443174695599879

theorem tailTrace_2862115 : CollatzResearch.WordTrace tailWord_2862115 prefixEnd_2862115 1469640683443174695599879 := by
  unfold tailWord_2862115
  simp only [CollatzResearch.WordTrace]
  refine ⟨104389910026053640170931799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69593273350702426780621199 104389910026053640170931799)
  ·
    refine ⟨156584865039080460256397699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104389910026053640170931799 156584865039080460256397699)
    ·
      refine ⟨234877297558620690384596549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156584865039080460256397699 234877297558620690384596549)
      ·
        refine ⟨44039493292241379447111853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 234877297558620690384596549 44039493292241379447111853)
        ·
          refine ⟨16514809984590517292666945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44039493292241379447111853 16514809984590517292666945)
          ·
            refine ⟨12386107488442887969500209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16514809984590517292666945 12386107488442887969500209)
            ·
              refine ⟨9289580616332165977125157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12386107488442887969500209 9289580616332165977125157)
              ·
                refine ⟨1741796365562281120710967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9289580616332165977125157 1741796365562281120710967)
                ·
                  refine ⟨2612694548343421681066451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1741796365562281120710967 2612694548343421681066451)
                  ·
                    refine ⟨3919041822515132521599677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2612694548343421681066451 3919041822515132521599677)
                    ·
                      refine ⟨1469640683443174695599879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3919041822515132521599677 1469640683443174695599879)
                      ·
                        rfl

theorem cell23_2862115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 4, 1, 1, 3].length) (baseStart_2862115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2862115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2862115 prefixEnd_2862115 := by exact prefixLift 2862115
  have htrace : WordTrace (prefixWord ++ tailWord_2862115) baseStart_2862115 baseEnd_2862115 := by
    simpa [prefixWord, tailWord_2862115, baseEnd_2862115] using wordTrace_append hprefix tailTrace_2862115
  have hstable : (prefixWord ++ tailWord_2862115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862115).length < 2 ^ (prefixWord ++ tailWord_2862115).sum := by decide
  have hdescent : baseEnd_2862115 < baseStart_2862115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862144 : List Nat := [2, 1, 1, 2, 2, 3, 3, 9]
def baseStart_2862144 : Nat := 118140960795 + 2862144 * 2 ^ 59
def prefixEnd_2862144 : Nat := 4983230072969 + 3 ^ 40 * 2862144 * 2
def baseEnd_2862144 : Nat := 54431687940079817856935

theorem tailTrace_2862144 : CollatzResearch.WordTrace tailWord_2862144 prefixEnd_2862144 54431687940079817856935 := by
  unfold tailWord_2862144
  simp only [CollatzResearch.WordTrace]
  refine ⟨52195483871474289061868743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69593978495299052082491657 52195483871474289061868743)
  ·
    refine ⟨78293225807211433592803115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52195483871474289061868743 78293225807211433592803115)
    ·
      refine ⟨117439838710817150389204673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78293225807211433592803115 117439838710817150389204673)
      ·
        refine ⟨88079879033112862791903505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117439838710817150389204673 88079879033112862791903505)
        ·
          refine ⟨66059909274834647093927629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88079879033112862791903505 66059909274834647093927629)
          ·
            refine ⟨24772465978062992660222861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66059909274834647093927629 24772465978062992660222861)
            ·
              refine ⟨9289674741773622247583573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24772465978062992660222861 9289674741773622247583573)
              ·
                refine ⟨54431687940079817856935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9289674741773622247583573 54431687940079817856935)
                ·
                  rfl

theorem cell23_2862144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 9].length) (baseStart_2862144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2862144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2862144 prefixEnd_2862144 := by exact prefixLift 2862144
  have htrace : WordTrace (prefixWord ++ tailWord_2862144) baseStart_2862144 baseEnd_2862144 := by
    simpa [prefixWord, tailWord_2862144, baseEnd_2862144] using wordTrace_append hprefix tailTrace_2862144
  have hstable : (prefixWord ++ tailWord_2862144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862144).length < 2 ^ (prefixWord ++ tailWord_2862144).sum := by decide
  have hdescent : baseEnd_2862144 < baseStart_2862144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862158 : List Nat := [4, 1, 1, 1, 1, 3, 1, 5, 1, 2, 3]
def baseStart_2862158 : Nat := 118140960795 + 2862158 * 2 ^ 59
def prefixEnd_2862158 : Nat := 4983230072969 + 3 ^ 40 * 2862158 * 2
def baseEnd_2862158 : Nat := 1469662763111318027362181

theorem tailTrace_2862158 : CollatzResearch.WordTrace tailWord_2862158 prefixEnd_2862158 1469662763111318027362181 := by
  unfold tailWord_2862158
  simp only [CollatzResearch.WordTrace]
  refine ⟨13048934795612232314343391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69594318909931905676498085 13048934795612232314343391)
  ·
    refine ⟨19573402193418348471515087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13048934795612232314343391 19573402193418348471515087)
    ·
      refine ⟨29360103290127522707272631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19573402193418348471515087 29360103290127522707272631)
      ·
        refine ⟨44040154935191284060908947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29360103290127522707272631 44040154935191284060908947)
        ·
          refine ⟨66060232402786926091363421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44040154935191284060908947 66060232402786926091363421)
          ·
            refine ⟨24772587151045097284261283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66060232402786926091363421 24772587151045097284261283)
            ·
              refine ⟨37158880726567645926391925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24772587151045097284261283 37158880726567645926391925)
              ·
                refine ⟨3483645068115716805599243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37158880726567645926391925 3483645068115716805599243)
                ·
                  refine ⟨5225467602173575208398865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3483645068115716805599243 5225467602173575208398865)
                  ·
                    refine ⟨3919100701630181406299149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5225467602173575208398865 3919100701630181406299149)
                    ·
                      refine ⟨1469662763111318027362181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3919100701630181406299149 1469662763111318027362181)
                      ·
                        rfl

theorem cell23_2862158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 5, 1, 2, 3].length) (baseStart_2862158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2862158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2862158 prefixEnd_2862158 := by exact prefixLift 2862158
  have htrace : WordTrace (prefixWord ++ tailWord_2862158) baseStart_2862158 baseEnd_2862158 := by
    simpa [prefixWord, tailWord_2862158, baseEnd_2862158] using wordTrace_append hprefix tailTrace_2862158
  have hstable : (prefixWord ++ tailWord_2862158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862158).length < 2 ^ (prefixWord ++ tailWord_2862158).sum := by decide
  have hdescent : baseEnd_2862158 < baseStart_2862158 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862166 : List Nat := [5, 2, 2, 1, 3, 1, 1, 1, 3, 1, 3]
def baseStart_2862166 : Nat := 118140960795 + 2862166 * 2 ^ 59
def prefixEnd_2862166 : Nat := 4983230072969 + 3 ^ 40 * 2862166 * 2
def baseEnd_2862166 : Nat := 1469666870956553996062145

theorem tailTrace_2862166 : CollatzResearch.WordTrace tailWord_2862166 prefixEnd_2862166 1469666870956553996062145 := by
  unfold tailWord_2862166
  simp only [CollatzResearch.WordTrace]
  refine ⟨6524485634304304742564897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69594513432579250587358901 6524485634304304742564897)
  ·
    refine ⟨4893364225728228556923673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6524485634304304742564897 4893364225728228556923673)
    ·
      refine ⟨3670023169296171417692755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4893364225728228556923673 3670023169296171417692755)
      ·
        refine ⟨5505034753944257126539133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3670023169296171417692755 5505034753944257126539133)
        ·
          refine ⟨2064388032729096422452175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5505034753944257126539133 2064388032729096422452175)
          ·
            refine ⟨3096582049093644633678263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2064388032729096422452175 3096582049093644633678263)
            ·
              refine ⟨4644873073640466950517395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3096582049093644633678263 4644873073640466950517395)
              ·
                refine ⟨6967309610460700425776093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4644873073640466950517395 6967309610460700425776093)
                ·
                  refine ⟨2612741103922762659666035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6967309610460700425776093 2612741103922762659666035)
                  ·
                    refine ⟨3919111655884143989499053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2612741103922762659666035 3919111655884143989499053)
                    ·
                      refine ⟨1469666870956553996062145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3919111655884143989499053 1469666870956553996062145)
                      ·
                        rfl

theorem cell23_2862166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_2862166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2862166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2862166 prefixEnd_2862166 := by exact prefixLift 2862166
  have htrace : WordTrace (prefixWord ++ tailWord_2862166) baseStart_2862166 baseEnd_2862166 := by
    simpa [prefixWord, tailWord_2862166, baseEnd_2862166] using wordTrace_append hprefix tailTrace_2862166
  have hstable : (prefixWord ++ tailWord_2862166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862166).length < 2 ^ (prefixWord ++ tailWord_2862166).sum := by decide
  have hdescent : baseEnd_2862166 < baseStart_2862166 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862178 : List Nat := [3, 3, 2, 2, 1, 2, 2, 8]
def baseStart_2862178 : Nat := 118140960795 + 2862178 * 2 ^ 59
def prefixEnd_2862178 : Nat := 4983230072969 + 3 ^ 40 * 2862178 * 2
def baseEnd_2862178 : Nat := 54432334545348442559707

theorem tailTrace_2862178 : CollatzResearch.WordTrace tailWord_2862178 prefixEnd_2862178 54432334545348442559707 := by
  unfold tailWord_2862178
  simp only [CollatzResearch.WordTrace]
  refine ⟨26098051956206350482618797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69594805216550267953650125 26098051956206350482618797)
  ·
    refine ⟨9786769483577381430982049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26098051956206350482618797 9786769483577381430982049)
    ·
      refine ⟨7340077112683036073236537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9786769483577381430982049 7340077112683036073236537)
      ·
        refine ⟨5505057834512277054927403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7340077112683036073236537 5505057834512277054927403)
        ·
          refine ⟨8257586751768415582391105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5505057834512277054927403 8257586751768415582391105)
          ·
            refine ⟨6193190063826311686793329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8257586751768415582391105 6193190063826311686793329)
            ·
              refine ⟨4644892547869733765094997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6193190063826311686793329 4644892547869733765094997)
              ·
                refine ⟨54432334545348442559707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4644892547869733765094997 54432334545348442559707)
                ·
                  rfl

theorem cell23_2862178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 8].length) (baseStart_2862178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2862178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2862178 prefixEnd_2862178 := by exact prefixLift 2862178
  have htrace : WordTrace (prefixWord ++ tailWord_2862178) baseStart_2862178 baseEnd_2862178 := by
    simpa [prefixWord, tailWord_2862178, baseEnd_2862178] using wordTrace_append hprefix tailTrace_2862178
  have hstable : (prefixWord ++ tailWord_2862178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862178).length < 2 ^ (prefixWord ++ tailWord_2862178).sum := by decide
  have hdescent : baseEnd_2862178 < baseStart_2862178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862206 : List Nat := [4, 2, 4, 1, 1, 1, 3, 1, 1, 1, 4]
def baseStart_2862206 : Nat := 118140960795 + 2862206 * 2 ^ 59
def prefixEnd_2862206 : Nat := 4983230072969 + 3 ^ 40 * 2862206 * 2
def baseEnd_2862206 : Nat := 1469687410182733839561961

theorem tailTrace_2862206 : CollatzResearch.WordTrace tailWord_2862206 prefixEnd_2862206 1469687410182733839561961 := by
  unfold tailWord_2862206
  simp only [CollatzResearch.WordTrace]
  refine ⟨13049153633590495339061809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69595486045815975141662981 13049153633590495339061809)
  ·
    refine ⟨9786865225192871504296357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13049153633590495339061809 9786865225192871504296357)
    ·
      refine ⟨1835037229723663407055567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9786865225192871504296357 1835037229723663407055567)
      ·
        refine ⟨2752555844585495110583351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1835037229723663407055567 2752555844585495110583351)
        ·
          refine ⟨4128833766878242665875027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2752555844585495110583351 4128833766878242665875027)
          ·
            refine ⟨6193250650317363998812541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4128833766878242665875027 6193250650317363998812541)
            ·
              refine ⟨2322468993869011499554703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6193250650317363998812541 2322468993869011499554703)
              ·
                refine ⟨3483703490803517249332055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2322468993869011499554703 3483703490803517249332055)
                ·
                  refine ⟨5225555236205275873998083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3483703490803517249332055 5225555236205275873998083)
                  ·
                    refine ⟨7838332854307913810997125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5225555236205275873998083 7838332854307913810997125)
                    ·
                      refine ⟨1469687410182733839561961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7838332854307913810997125 1469687410182733839561961)
                      ·
                        rfl

theorem cell23_2862206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_2862206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2862206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2862206 prefixEnd_2862206 := by exact prefixLift 2862206
  have htrace : WordTrace (prefixWord ++ tailWord_2862206) baseStart_2862206 baseEnd_2862206 := by
    simpa [prefixWord, tailWord_2862206, baseEnd_2862206] using wordTrace_append hprefix tailTrace_2862206
  have hstable : (prefixWord ++ tailWord_2862206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862206).length < 2 ^ (prefixWord ++ tailWord_2862206).sum := by decide
  have hdescent : baseEnd_2862206 < baseStart_2862206 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862222 : List Nat := [4, 1, 1, 3, 2, 2, 2, 2, 2, 1, 3]
def baseStart_2862222 : Nat := 118140960795 + 2862222 * 2 ^ 59
def prefixEnd_2862222 : Nat := 4983230072969 + 3 ^ 40 * 2862222 * 2
def baseEnd_2862222 : Nat := 1469695625873205776961887

theorem tailTrace_2862222 : CollatzResearch.WordTrace tailWord_2862222 prefixEnd_2862222 1469695625873205776961887 := by
  unfold tailWord_2862222
  simp only [CollatzResearch.WordTrace]
  refine ⟨13049226579583249680634615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69595875091110664963384613 13049226579583249680634615)
  ·
    refine ⟨19573839869374874520951923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13049226579583249680634615 19573839869374874520951923)
    ·
      refine ⟨29360759804062311781427885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19573839869374874520951923 29360759804062311781427885)
      ·
        refine ⟨11010284926523366918035457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29360759804062311781427885 11010284926523366918035457)
        ·
          refine ⟨8257713694892525188526593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11010284926523366918035457 8257713694892525188526593)
          ·
            refine ⟨6193285271169393891394945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8257713694892525188526593 6193285271169393891394945)
            ·
              refine ⟨4644963953377045418546209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6193285271169393891394945 4644963953377045418546209)
              ·
                refine ⟨3483722965032784063909657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4644963953377045418546209 3483722965032784063909657)
                ·
                  refine ⟨2612792223774588047932243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3483722965032784063909657 2612792223774588047932243)
                  ·
                    refine ⟨3919188335661882071898365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2612792223774588047932243 3919188335661882071898365)
                    ·
                      refine ⟨1469695625873205776961887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3919188335661882071898365 1469695625873205776961887)
                      ·
                        rfl

theorem cell23_2862222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_2862222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2862222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2862222 prefixEnd_2862222 := by exact prefixLift 2862222
  have htrace : WordTrace (prefixWord ++ tailWord_2862222) baseStart_2862222 baseEnd_2862222 := by
    simpa [prefixWord, tailWord_2862222, baseEnd_2862222] using wordTrace_append hprefix tailTrace_2862222
  have hstable : (prefixWord ++ tailWord_2862222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862222).length < 2 ^ (prefixWord ++ tailWord_2862222).sum := by decide
  have hdescent : baseEnd_2862222 < baseStart_2862222 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862238 : List Nat := [4, 3, 1, 1, 2, 1, 1, 1, 1, 8]
def baseStart_2862238 : Nat := 118140960795 + 2862238 * 2 ^ 59
def prefixEnd_2862238 : Nat := 4983230072969 + 3 ^ 40 * 2862238 * 2
def baseEnd_2862238 : Nat := 489901280521225904787271

theorem tailTrace_2862238 : CollatzResearch.WordTrace tailWord_2862238 prefixEnd_2862238 489901280521225904787271 := by
  unfold tailWord_2862238
  simp only [CollatzResearch.WordTrace]
  refine ⟨13049299525576004022207421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69596264136405354785106245 13049299525576004022207421)
  ·
    refine ⟨4893487322091001508327783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13049299525576004022207421 4893487322091001508327783)
    ·
      refine ⟨7340230983136502262491675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4893487322091001508327783 7340230983136502262491675)
      ·
        refine ⟨11010346474704753393737513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7340230983136502262491675 11010346474704753393737513)
        ·
          refine ⟨8257759856028565045303135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11010346474704753393737513 8257759856028565045303135)
          ·
            refine ⟨12386639784042847567954703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8257759856028565045303135 12386639784042847567954703)
            ·
              refine ⟨18579959676064271351932055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12386639784042847567954703 18579959676064271351932055)
              ·
                refine ⟨27869939514096407027898083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18579959676064271351932055 27869939514096407027898083)
                ·
                  refine ⟨41804909271144610541847125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27869939514096407027898083 41804909271144610541847125)
                  ·
                    refine ⟨489901280521225904787271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 41804909271144610541847125 489901280521225904787271)
                    ·
                      rfl

theorem cell23_2862238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_2862238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2862238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2862238 prefixEnd_2862238 := by exact prefixLift 2862238
  have htrace : WordTrace (prefixWord ++ tailWord_2862238) baseStart_2862238 baseEnd_2862238 := by
    simpa [prefixWord, tailWord_2862238, baseEnd_2862238] using wordTrace_append hprefix tailTrace_2862238
  have hstable : (prefixWord ++ tailWord_2862238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862238).length < 2 ^ (prefixWord ++ tailWord_2862238).sum := by decide
  have hdescent : baseEnd_2862238 < baseStart_2862238 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862245 : List Nat := [1, 3, 1, 2, 1, 5, 2, 1, 1, 4, 2]
def baseStart_2862245 : Nat := 118140960795 + 2862245 * 2 ^ 59
def prefixEnd_2862245 : Nat := 4983230072969 + 3 ^ 40 * 2862245 * 2
def baseEnd_2862245 : Nat := 1469707435928259186974281

theorem tailTrace_2862245 : CollatzResearch.WordTrace tailWord_2862245 prefixEnd_2862245 1469707435928259186974281 := by
  unfold tailWord_2862245
  simp only [CollatzResearch.WordTrace]
  refine ⟨104394651515582672373164189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69596434343721781582109459 104394651515582672373164189)
  ·
    refine ⟨39147994318343502139936571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104394651515582672373164189 39147994318343502139936571)
    ·
      refine ⟨58721991477515253209904857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39147994318343502139936571 58721991477515253209904857)
      ·
        refine ⟨44041493608136439907428643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58721991477515253209904857 44041493608136439907428643)
        ·
          refine ⟨66062240412204659861142965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44041493608136439907428643 66062240412204659861142965)
          ·
            refine ⟨6193335038644186861982153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 66062240412204659861142965 6193335038644186861982153)
            ·
              refine ⟨4645001278983140146486615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6193335038644186861982153 4645001278983140146486615)
              ·
                refine ⟨6967501918474710219729923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4645001278983140146486615 6967501918474710219729923)
                ·
                  refine ⟨10451252877712065329594885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6967501918474710219729923 10451252877712065329594885)
                  ·
                    refine ⟨1959609914571012249299041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10451252877712065329594885 1959609914571012249299041)
                    ·
                      refine ⟨1469707435928259186974281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1959609914571012249299041 1469707435928259186974281)
                      ·
                        rfl

theorem cell23_2862245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 1, 1, 4, 2].length) (baseStart_2862245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2862245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2862245 prefixEnd_2862245 := by exact prefixLift 2862245
  have htrace : WordTrace (prefixWord ++ tailWord_2862245) baseStart_2862245 baseEnd_2862245 := by
    simpa [prefixWord, tailWord_2862245, baseEnd_2862245] using wordTrace_append hprefix tailTrace_2862245
  have hstable : (prefixWord ++ tailWord_2862245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862245).length < 2 ^ (prefixWord ++ tailWord_2862245).sum := by decide
  have hdescent : baseEnd_2862245 < baseStart_2862245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862318 : List Nat := [4, 1, 2, 1, 1, 1, 4, 1, 1, 3, 4]
def baseStart_2862318 : Nat := 118140960795 + 2862318 * 2 ^ 59
def prefixEnd_2862318 : Nat := 4983230072969 + 3 ^ 40 * 2862318 * 2
def baseEnd_2862318 : Nat := 1469744920016037401361445

theorem tailTrace_2862318 : CollatzResearch.WordTrace tailWord_2862318 prefixEnd_2862318 1469744920016037401361445 := by
  unfold tailWord_2862318
  simp only [CollatzResearch.WordTrace]
  refine ⟨13049664255539775730071451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69598209362878803893714405 13049664255539775730071451)
  ·
    refine ⟨19574496383309663595107177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13049664255539775730071451 19574496383309663595107177)
    ·
      refine ⟨14680872287482247696330383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19574496383309663595107177 14680872287482247696330383)
      ·
        refine ⟨22021308431223371544495575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14680872287482247696330383 22021308431223371544495575)
        ·
          refine ⟨33031962646835057316743363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22021308431223371544495575 33031962646835057316743363)
          ·
            refine ⟨49547943970252585975115045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33031962646835057316743363 49547943970252585975115045)
            ·
              refine ⟨9290239494422359870334071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49547943970252585975115045 9290239494422359870334071)
              ·
                refine ⟨13935359241633539805501107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9290239494422359870334071 13935359241633539805501107)
                ·
                  refine ⟨20903038862450309708251661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13935359241633539805501107 20903038862450309708251661)
                  ·
                    refine ⟨7838639573418866140594373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20903038862450309708251661 7838639573418866140594373)
                    ·
                      refine ⟨1469744920016037401361445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7838639573418866140594373 1469744920016037401361445)
                      ·
                        rfl

theorem cell23_2862318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_2862318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2862318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2862318 prefixEnd_2862318 := by exact prefixLift 2862318
  have htrace : WordTrace (prefixWord ++ tailWord_2862318) baseStart_2862318 baseEnd_2862318 := by
    simpa [prefixWord, tailWord_2862318, baseEnd_2862318] using wordTrace_append hprefix tailTrace_2862318
  have hstable : (prefixWord ++ tailWord_2862318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862318).length < 2 ^ (prefixWord ++ tailWord_2862318).sum := by decide
  have hdescent : baseEnd_2862318 < baseStart_2862318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862321 : List Nat := [1, 2, 2, 2, 2, 1, 1, 2, 2, 3, 5]
def baseStart_2862321 : Nat := 118140960795 + 2862321 * 2 ^ 59
def prefixEnd_2862321 : Nat := 4983230072969 + 3 ^ 40 * 2862321 * 2
def baseEnd_2862321 : Nat := 1469746460458000889623931

theorem tailTrace_2862321 : CollatzResearch.WordTrace tailWord_2862321 prefixEnd_2862321 1469746460458000889623931 := by
  unfold tailWord_2862321
  simp only [CollatzResearch.WordTrace]
  refine ⟨104397423463307337352930817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69598282308871558235287211 104397423463307337352930817)
  ·
    refine ⟨78298067597480503014698113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104397423463307337352930817 78298067597480503014698113)
    ·
      refine ⟨58723550698110377261023585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78298067597480503014698113 58723550698110377261023585)
      ·
        refine ⟨44042663023582782945767689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58723550698110377261023585 44042663023582782945767689)
        ·
          refine ⟨33031997267687087209325767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44042663023582782945767689 33031997267687087209325767)
          ·
            refine ⟨49547995901530630813988651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33031997267687087209325767 49547995901530630813988651)
            ·
              refine ⟨74321993852295946220982977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49547995901530630813988651 74321993852295946220982977)
              ·
                refine ⟨55741495389221959665737233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74321993852295946220982977 55741495389221959665737233)
                ·
                  refine ⟨41806121541916469749302925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55741495389221959665737233 41806121541916469749302925)
                  ·
                    refine ⟨15677295578218676155988597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41806121541916469749302925 15677295578218676155988597)
                    ·
                      refine ⟨1469746460458000889623931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15677295578218676155988597 1469746460458000889623931)
                      ·
                        rfl

theorem cell23_2862321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_2862321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2862321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2862321 prefixEnd_2862321 := by exact prefixLift 2862321
  have htrace : WordTrace (prefixWord ++ tailWord_2862321) baseStart_2862321 baseEnd_2862321 := by
    simpa [prefixWord, tailWord_2862321, baseEnd_2862321] using wordTrace_append hprefix tailTrace_2862321
  have hstable : (prefixWord ++ tailWord_2862321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862321).length < 2 ^ (prefixWord ++ tailWord_2862321).sum := by decide
  have hdescent : baseEnd_2862321 < baseStart_2862321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862341 : List Nat := [1, 3, 1, 1, 2, 1, 3, 3, 8]
def baseStart_2862341 : Nat := 118140960795 + 2862341 * 2 ^ 59
def prefixEnd_2862341 : Nat := 4983230072969 + 3 ^ 40 * 2862341 * 2
def baseEnd_2862341 : Nat := 163306303341232312374871

theorem tailTrace_2862341 : CollatzResearch.WordTrace tailWord_2862341 prefixEnd_2862341 163306303341232312374871 := by
  unfold tailWord_2862341
  simp only [CollatzResearch.WordTrace]
  refine ⟨104398152923234880768658877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69598768615489920512439251 104398152923234880768658877)
  ·
    refine ⟨39149307346213080288247079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104398152923234880768658877 39149307346213080288247079)
    ·
      refine ⟨58723961019319620432370619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39149307346213080288247079 58723961019319620432370619)
      ·
        refine ⟨88085941528979430648555929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58723961019319620432370619 88085941528979430648555929)
        ·
          refine ⟨66064456146734572986416947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88085941528979430648555929 66064456146734572986416947)
          ·
            refine ⟨99096684220101859479625421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66064456146734572986416947 99096684220101859479625421)
            ·
              refine ⟨37161256582538197304859533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99096684220101859479625421 37161256582538197304859533)
              ·
                refine ⟨13935471218451823989322325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37161256582538197304859533 13935471218451823989322325)
                ·
                  refine ⟨163306303341232312374871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13935471218451823989322325 163306303341232312374871)
                  ·
                    rfl

theorem cell23_2862341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 8].length) (baseStart_2862341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2862341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2862341 prefixEnd_2862341 := by exact prefixLift 2862341
  have htrace : WordTrace (prefixWord ++ tailWord_2862341) baseStart_2862341 baseEnd_2862341 := by
    simpa [prefixWord, tailWord_2862341, baseEnd_2862341] using wordTrace_append hprefix tailTrace_2862341
  have hstable : (prefixWord ++ tailWord_2862341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862341).length < 2 ^ (prefixWord ++ tailWord_2862341).sum := by decide
  have hdescent : baseEnd_2862341 < baseStart_2862341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862439 : List Nat := [1, 1, 5, 1, 4, 2, 2, 1, 1, 5]
def baseStart_2862439 : Nat := 118140960795 + 2862439 * 2 ^ 59
def prefixEnd_2862439 : Nat := 4983230072969 + 3 ^ 40 * 2862439 * 2
def baseEnd_2862439 : Nat := 489935683725077142649463

theorem tailTrace_2862439 : CollatzResearch.WordTrace tailWord_2862439 prefixEnd_2862439 489935683725077142649463 := by
  unfold tailWord_2862439
  simp only [CollatzResearch.WordTrace]
  refine ⟨104401727276879843505726371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69601151517919895670484247 104401727276879843505726371)
  ·
    refine ⟨156602590915319765258589557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104401727276879843505726371 156602590915319765258589557)
    ·
      refine ⟨14681492898311227992992771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 156602590915319765258589557 14681492898311227992992771)
      ·
        refine ⟨22022239347466841989489157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14681492898311227992992771 22022239347466841989489157)
        ·
          refine ⟨4129169877650032873029217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22022239347466841989489157 4129169877650032873029217)
          ·
            refine ⟨3096877408237524654771913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4129169877650032873029217 3096877408237524654771913)
            ·
              refine ⟨2322658056178143491078935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3096877408237524654771913 2322658056178143491078935)
              ·
                refine ⟨3483987084267215236618403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2322658056178143491078935 3483987084267215236618403)
                ·
                  refine ⟨5225980626400822854927605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3483987084267215236618403 5225980626400822854927605)
                  ·
                    refine ⟨489935683725077142649463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5225980626400822854927605 489935683725077142649463)
                    ·
                      rfl

theorem cell23_2862439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 2, 1, 1, 5].length) (baseStart_2862439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2862439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2862439 prefixEnd_2862439 := by exact prefixLift 2862439
  have htrace : WordTrace (prefixWord ++ tailWord_2862439) baseStart_2862439 baseEnd_2862439 := by
    simpa [prefixWord, tailWord_2862439, baseEnd_2862439] using wordTrace_append hprefix tailTrace_2862439
  have hstable : (prefixWord ++ tailWord_2862439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862439).length < 2 ^ (prefixWord ++ tailWord_2862439).sum := by decide
  have hdescent : baseEnd_2862439 < baseStart_2862439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862459 : List Nat := [1, 1, 1, 1, 1, 6, 1, 6, 1, 2, 2]
def baseStart_2862459 : Nat := 118140960795 + 2862459 * 2 ^ 59
def prefixEnd_2862459 : Nat := 4983230072969 + 3 ^ 40 * 2862459 * 2
def baseEnd_2862459 : Nat := 1469817320788321349698297

theorem tailTrace_2862459 : CollatzResearch.WordTrace tailWord_2862459 prefixEnd_2862459 1469817320788321349698297 := by
  unfold tailWord_2862459
  simp only [CollatzResearch.WordTrace]
  refine ⟨104402456736807386921454431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69601637824538257947636287 104402456736807386921454431)
  ·
    refine ⟨156603685105211080382181647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104402456736807386921454431 156603685105211080382181647)
    ·
      refine ⟨234905527657816620573272471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156603685105211080382181647 234905527657816620573272471)
      ·
        refine ⟨352358291486724930859908707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234905527657816620573272471 352358291486724930859908707)
        ·
          refine ⟨528537437230087396289863061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 352358291486724930859908707 528537437230087396289863061)
          ·
            refine ⟨24775192370160346701087331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 528537437230087396289863061 24775192370160346701087331)
            ·
              refine ⟨37162788555240520051630997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24775192370160346701087331 37162788555240520051630997)
              ·
                refine ⟨1742005713526899377420203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 37162788555240520051630997 1742005713526899377420203)
                ·
                  refine ⟨2613008570290349066130305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1742005713526899377420203 2613008570290349066130305)
                  ·
                    refine ⟨1959756427717761799597729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2613008570290349066130305 1959756427717761799597729)
                    ·
                      refine ⟨1469817320788321349698297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1959756427717761799597729 1469817320788321349698297)
                      ·
                        rfl

theorem cell23_2862459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 6, 1, 2, 2].length) (baseStart_2862459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2862459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2862459 prefixEnd_2862459 := by exact prefixLift 2862459
  have htrace : WordTrace (prefixWord ++ tailWord_2862459) baseStart_2862459 baseEnd_2862459 := by
    simpa [prefixWord, tailWord_2862459, baseEnd_2862459] using wordTrace_append hprefix tailTrace_2862459
  have hstable : (prefixWord ++ tailWord_2862459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862459).length < 2 ^ (prefixWord ++ tailWord_2862459).sum := by decide
  have hdescent : baseEnd_2862459 < baseStart_2862459 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862472 : List Nat := [2, 1, 3, 3, 1, 4, 1, 1, 1, 2, 4]
def baseStart_2862472 : Nat := 118140960795 + 2862472 * 2 ^ 59
def prefixEnd_2862472 : Nat := 4983230072969 + 3 ^ 40 * 2862472 * 2
def baseEnd_2862472 : Nat := 1469823996036829798835737

theorem tailTrace_2862472 : CollatzResearch.WordTrace tailWord_2862472 prefixEnd_2862472 1469823996036829798835737 := by
  unfold tailWord_2862472
  simp only [CollatzResearch.WordTrace]
  refine ⟨52201465442880145070838835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69601953923840193427785113 52201465442880145070838835)
  ·
    refine ⟨78302198164320217606258253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52201465442880145070838835 78302198164320217606258253)
    ·
      refine ⟨29363324311620081602346845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78302198164320217606258253 29363324311620081602346845)
      ·
        refine ⟨11011246616857530600880067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29363324311620081602346845 11011246616857530600880067)
        ·
          refine ⟨16516869925286295901320101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11011246616857530600880067 16516869925286295901320101)
          ·
            refine ⟨3096913110991180481497519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16516869925286295901320101 3096913110991180481497519)
            ·
              refine ⟨4645369666486770722246279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3096913110991180481497519 4645369666486770722246279)
              ·
                refine ⟨6968054499730156083369419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4645369666486770722246279 6968054499730156083369419)
                ·
                  refine ⟨10452081749595234125054129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6968054499730156083369419 10452081749595234125054129)
                  ·
                    refine ⟨7839061312196425593790597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10452081749595234125054129 7839061312196425593790597)
                    ·
                      refine ⟨1469823996036829798835737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7839061312196425593790597 1469823996036829798835737)
                      ·
                        rfl

theorem cell23_2862472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_2862472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2862472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2862472 prefixEnd_2862472 := by exact prefixLift 2862472
  have htrace : WordTrace (prefixWord ++ tailWord_2862472) baseStart_2862472 baseEnd_2862472 := by
    simpa [prefixWord, tailWord_2862472, baseEnd_2862472] using wordTrace_append hprefix tailTrace_2862472
  have hstable : (prefixWord ++ tailWord_2862472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862472).length < 2 ^ (prefixWord ++ tailWord_2862472).sum := by decide
  have hdescent : baseEnd_2862472 < baseStart_2862472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862482 : List Nat := [3, 2, 3, 3, 1, 1, 1, 9]
def baseStart_2862482 : Nat := 118140960795 + 2862482 * 2 ^ 59
def prefixEnd_2862482 : Nat := 4983230072969 + 3 ^ 40 * 2862482 * 2
def baseEnd_2862482 : Nat := 54438115957162028137433

theorem tailTrace_2862482 : CollatzResearch.WordTrace tailWord_2862482 prefixEnd_2862482 54438115957162028137433 := by
  unfold tailWord_2862482
  simp only [CollatzResearch.WordTrace]
  refine ⟨26100823903931015462385425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69602197077149374566361133 26100823903931015462385425)
  ·
    refine ⟨19575617927948261596789069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26100823903931015462385425 19575617927948261596789069)
    ·
      refine ⟨7340856722980598098795901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19575617927948261596789069 7340856722980598098795901)
      ·
        refine ⟨2752821271117724287048463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7340856722980598098795901 2752821271117724287048463)
        ·
          refine ⟨4129231906676586430572695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2752821271117724287048463 4129231906676586430572695)
          ·
            refine ⟨6193847860014879645859043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4129231906676586430572695 6193847860014879645859043)
            ·
              refine ⟨9290771790022319468788565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6193847860014879645859043 9290771790022319468788565)
              ·
                refine ⟨54438115957162028137433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9290771790022319468788565 54438115957162028137433)
                ·
                  rfl

theorem cell23_2862482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 9].length) (baseStart_2862482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2862482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2862482 prefixEnd_2862482 := by exact prefixLift 2862482
  have htrace : WordTrace (prefixWord ++ tailWord_2862482) baseStart_2862482 baseEnd_2862482 := by
    simpa [prefixWord, tailWord_2862482, baseEnd_2862482] using wordTrace_append hprefix tailTrace_2862482
  have hstable : (prefixWord ++ tailWord_2862482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862482).length < 2 ^ (prefixWord ++ tailWord_2862482).sum := by decide
  have hdescent : baseEnd_2862482 < baseStart_2862482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862493 : List Nat := [1, 4, 2, 1, 3, 3, 1, 3, 1, 2, 2]
def baseStart_2862493 : Nat := 118140960795 + 2862493 * 2 ^ 59
def prefixEnd_2862493 : Nat := 4983230072969 + 3 ^ 40 * 2862493 * 2
def baseEnd_2862493 : Nat := 1469834779130574216673141

theorem tailTrace_2862493 : CollatzResearch.WordTrace tailWord_2862493 prefixEnd_2862493 1469834779130574216673141 := by
  unfold tailWord_2862493
  simp only [CollatzResearch.WordTrace]
  refine ⟨104403696818684210728192133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69602464545789473818794755 104403696818684210728192133)
  ·
    refine ⟨19575693153503289511536025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104403696818684210728192133 19575693153503289511536025)
    ·
      refine ⟨14681769865127467133652019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19575693153503289511536025 14681769865127467133652019)
      ·
        refine ⟨22022654797691200700478029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14681769865127467133652019 22022654797691200700478029)
        ·
          refine ⟨8258495549134200262679261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22022654797691200700478029 8258495549134200262679261)
          ·
            refine ⟨3096935830925325098504723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8258495549134200262679261 3096935830925325098504723)
            ·
              refine ⟨4645403746387987647757085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3096935830925325098504723 4645403746387987647757085)
              ·
                refine ⟨1742026404895495367908907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4645403746387987647757085 1742026404895495367908907)
                ·
                  refine ⟨2613039607343243051863361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1742026404895495367908907 2613039607343243051863361)
                  ·
                    refine ⟨1959779705507432288897521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2613039607343243051863361 1959779705507432288897521)
                    ·
                      refine ⟨1469834779130574216673141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1959779705507432288897521 1469834779130574216673141)
                      ·
                        rfl

theorem cell23_2862493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 3, 1, 2, 2].length) (baseStart_2862493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2862493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2862493 prefixEnd_2862493 := by exact prefixLift 2862493
  have htrace : WordTrace (prefixWord ++ tailWord_2862493) baseStart_2862493 baseEnd_2862493 := by
    simpa [prefixWord, tailWord_2862493, baseEnd_2862493] using wordTrace_append hprefix tailTrace_2862493
  have hstable : (prefixWord ++ tailWord_2862493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862493).length < 2 ^ (prefixWord ++ tailWord_2862493).sum := by decide
  have hdescent : baseEnd_2862493 < baseStart_2862493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862508 : List Nat := [2, 2, 1, 1, 1, 1, 4, 1, 4, 6]
def baseStart_2862508 : Nat := 118140960795 + 2862508 * 2 ^ 59
def prefixEnd_2862508 : Nat := 4983230072969 + 3 ^ 40 * 2862508 * 2
def baseEnd_2862508 : Nat := 489947493780130552661857

theorem tailTrace_2862508 : CollatzResearch.WordTrace tailWord_2862508 prefixEnd_2862508 489947493780130552661857 := by
  unfold tailWord_2862508
  simp only [CollatzResearch.WordTrace]
  refine ⟨52202121956814934144994089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69602829275753245526658785 52202121956814934144994089)
  ·
    refine ⟨39151591467611200608745567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52202121956814934144994089 39151591467611200608745567)
    ·
      refine ⟨58727387201416800913118351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39151591467611200608745567 58727387201416800913118351)
      ·
        refine ⟨88091080802125201369677527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58727387201416800913118351 88091080802125201369677527)
        ·
          refine ⟨132136621203187802054516291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88091080802125201369677527 132136621203187802054516291)
          ·
            refine ⟨198204931804781703081774437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132136621203187802054516291 198204931804781703081774437)
            ·
              refine ⟨37163424713396569327832707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 198204931804781703081774437 37163424713396569327832707)
              ·
                refine ⟨55745137070094853991749061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37163424713396569327832707 55745137070094853991749061)
                ·
                  refine ⟨10452213200642785123452949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55745137070094853991749061 10452213200642785123452949)
                  ·
                    refine ⟨489947493780130552661857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10452213200642785123452949 489947493780130552661857)
                    ·
                      rfl

theorem cell23_2862508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 6].length) (baseStart_2862508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2862508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2862508 prefixEnd_2862508 := by exact prefixLift 2862508
  have htrace : WordTrace (prefixWord ++ tailWord_2862508) baseStart_2862508 baseEnd_2862508 := by
    simpa [prefixWord, tailWord_2862508, baseEnd_2862508] using wordTrace_append hprefix tailTrace_2862508
  have hstable : (prefixWord ++ tailWord_2862508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862508).length < 2 ^ (prefixWord ++ tailWord_2862508).sum := by decide
  have hdescent : baseEnd_2862508 < baseStart_2862508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862509 : List Nat := [1, 5, 2, 2, 1, 1, 2, 1, 4, 1, 3]
def baseStart_2862509 : Nat := 118140960795 + 2862509 * 2 ^ 59
def prefixEnd_2862509 : Nat := 4983230072969 + 3 ^ 40 * 2862509 * 2
def baseEnd_2862509 : Nat := 1469842994821046154073067

theorem tailTrace_2862509 : CollatzResearch.WordTrace tailWord_2862509 prefixEnd_2862509 1469842994821046154073067 := by
  unfold tailWord_2862509
  simp only [CollatzResearch.WordTrace]
  refine ⟨104404280386626245460774581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69602853591084163640516387 104404280386626245460774581)
  ·
    refine ⟨9787901286246210511947617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 104404280386626245460774581 9787901286246210511947617)
    ·
      refine ⟨7340925964684657883960713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9787901286246210511947617 7340925964684657883960713)
      ·
        refine ⟨5505694473513493412970535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7340925964684657883960713 5505694473513493412970535)
        ·
          refine ⟨8258541710270240119455803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5505694473513493412970535 8258541710270240119455803)
          ·
            refine ⟨12387812565405360179183705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8258541710270240119455803 12387812565405360179183705)
            ·
              refine ⟨9290859424054020134387779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12387812565405360179183705 9290859424054020134387779)
              ·
                refine ⟨13936289136081030201581669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9290859424054020134387779 13936289136081030201581669)
                ·
                  refine ⟨2613054213015193162796563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13936289136081030201581669 2613054213015193162796563)
                  ·
                    refine ⟨3919581319522789744194845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2613054213015193162796563 3919581319522789744194845)
                    ·
                      refine ⟨1469842994821046154073067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3919581319522789744194845 1469842994821046154073067)
                      ·
                        rfl

theorem cell23_2862509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_2862509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2862509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2862509 prefixEnd_2862509 := by exact prefixLift 2862509
  have htrace : WordTrace (prefixWord ++ tailWord_2862509) baseStart_2862509 baseEnd_2862509 := by
    simpa [prefixWord, tailWord_2862509, baseEnd_2862509] using wordTrace_append hprefix tailTrace_2862509
  have hstable : (prefixWord ++ tailWord_2862509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862509).length < 2 ^ (prefixWord ++ tailWord_2862509).sum := by decide
  have hdescent : baseEnd_2862509 < baseStart_2862509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862582 : List Nat := [5, 1, 1, 1, 2, 2, 1, 1, 1, 5, 3]
def baseStart_2862582 : Nat := 118140960795 + 2862582 * 2 ^ 59
def prefixEnd_2862582 : Nat := 4983230072969 + 3 ^ 40 * 2862582 * 2
def baseEnd_2862582 : Nat := 1469880478908824368460231

theorem tailTrace_2862582 : CollatzResearch.WordTrace tailWord_2862582 prefixEnd_2862582 1469880478908824368460231 := by
  unfold tailWord_2862582
  simp only [CollatzResearch.WordTrace]
  refine ⟨6525433932210111183011375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69604628610241185952121333 6525433932210111183011375)
  ·
    refine ⟨9788150898315166774517063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6525433932210111183011375 9788150898315166774517063)
    ·
      refine ⟨14682226347472750161775595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9788150898315166774517063 14682226347472750161775595)
      ·
        refine ⟨22023339521209125242663393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14682226347472750161775595 22023339521209125242663393)
        ·
          refine ⟨16517504640906843931997545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22023339521209125242663393 16517504640906843931997545)
          ·
            refine ⟨12388128480680132948998159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16517504640906843931997545 12388128480680132948998159)
            ·
              refine ⟨18582192721020199423497239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12388128480680132948998159 18582192721020199423497239)
              ·
                refine ⟨27873289081530299135245859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18582192721020199423497239 27873289081530299135245859)
                ·
                  refine ⟨41809933622295448702868789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27873289081530299135245859 41809933622295448702868789)
                  ·
                    refine ⟨3919681277090198315893949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41809933622295448702868789 3919681277090198315893949)
                    ·
                      refine ⟨1469880478908824368460231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3919681277090198315893949 1469880478908824368460231)
                      ·
                        rfl

theorem cell23_2862582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 1, 5, 3].length) (baseStart_2862582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2862582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2862582 prefixEnd_2862582 := by exact prefixLift 2862582
  have htrace : WordTrace (prefixWord ++ tailWord_2862582) baseStart_2862582 baseEnd_2862582 := by
    simpa [prefixWord, tailWord_2862582, baseEnd_2862582] using wordTrace_append hprefix tailTrace_2862582
  have hstable : (prefixWord ++ tailWord_2862582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862582).length < 2 ^ (prefixWord ++ tailWord_2862582).sum := by decide
  have hdescent : baseEnd_2862582 < baseStart_2862582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862602 : List Nat := [3, 1, 2, 2, 2, 2, 3, 1, 2, 5]
def baseStart_2862602 : Nat := 118140960795 + 2862602 * 2 ^ 59
def prefixEnd_2862602 : Nat := 4983230072969 + 3 ^ 40 * 2862602 * 2
def baseEnd_2862602 : Nat := 489963582840638096736713

theorem tailTrace_2862602 : CollatzResearch.WordTrace tailWord_2862602 prefixEnd_2862602 489963582840638096736713 := by
  unfold tailWord_2862602
  simp only [CollatzResearch.WordTrace]
  refine ⟨26101918093822330585977515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69605114916859548229273373 26101918093822330585977515)
  ·
    refine ⟨39152877140733495878966273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26101918093822330585977515 39152877140733495878966273)
    ·
      refine ⟨29364657855550121909224705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39152877140733495878966273 29364657855550121909224705)
      ·
        refine ⟨22023493391662591431918529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29364657855550121909224705 22023493391662591431918529)
        ·
          refine ⟨16517620043746943573938897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22023493391662591431918529 16517620043746943573938897)
          ·
            refine ⟨12388215032810207680454173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16517620043746943573938897 12388215032810207680454173)
            ·
              refine ⟨4645580637303827880170315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12388215032810207680454173 4645580637303827880170315)
              ·
                refine ⟨6968370955955741820255473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4645580637303827880170315 6968370955955741820255473)
                ·
                  refine ⟨5226278216966806365191605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6968370955955741820255473 5226278216966806365191605)
                  ·
                    refine ⟨489963582840638096736713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5226278216966806365191605 489963582840638096736713)
                    ·
                      rfl

theorem cell23_2862602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 1, 2, 5].length) (baseStart_2862602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2862602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2862602 prefixEnd_2862602 := by exact prefixLift 2862602
  have htrace : WordTrace (prefixWord ++ tailWord_2862602) baseStart_2862602 baseEnd_2862602 := by
    simpa [prefixWord, tailWord_2862602, baseEnd_2862602] using wordTrace_append hprefix tailTrace_2862602
  have hstable : (prefixWord ++ tailWord_2862602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862602).length < 2 ^ (prefixWord ++ tailWord_2862602).sum := by decide
  have hdescent : baseEnd_2862602 < baseStart_2862602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862696 : List Nat := [2, 1, 4, 3, 1, 3, 2, 1, 6]
def baseStart_2862696 : Nat := 118140960795 + 2862696 * 2 ^ 59
def prefixEnd_2862696 : Nat := 4983230072969 + 3 ^ 40 * 2862696 * 2
def baseEnd_2862696 : Nat := 163326557300381880270523

theorem tailTrace_2862696 : CollatzResearch.WordTrace tailWord_2862696 prefixEnd_2862696 163326557300381880270523 := by
  unfold tailWord_2862696
  simp only [CollatzResearch.WordTrace]
  refine ⟨52205550418474388198915971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69607400557965850931887961 52205550418474388198915971)
  ·
    refine ⟨78308325627711582298373957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52205550418474388198915971 78308325627711582298373957)
    ·
      refine ⟨14682811055195921680945117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78308325627711582298373957 14682811055195921680945117)
      ·
        refine ⟨5506054145698470630354419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14682811055195921680945117 5506054145698470630354419)
        ·
          refine ⟨8259081218547705945531629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5506054145698470630354419 8259081218547705945531629)
          ·
            refine ⟨3097155456955389729574361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8259081218547705945531629 3097155456955389729574361)
            ·
              refine ⟨2322866592716542297180771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3097155456955389729574361 2322866592716542297180771)
              ·
                refine ⟨3484299889074813445771157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2322866592716542297180771 3484299889074813445771157)
                ·
                  refine ⟨163326557300381880270523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3484299889074813445771157 163326557300381880270523)
                  ·
                    rfl

theorem cell23_2862696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 2, 1, 6].length) (baseStart_2862696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2862696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2862696 prefixEnd_2862696 := by exact prefixLift 2862696
  have htrace : WordTrace (prefixWord ++ tailWord_2862696) baseStart_2862696 baseEnd_2862696 := by
    simpa [prefixWord, tailWord_2862696, baseEnd_2862696] using wordTrace_append hprefix tailTrace_2862696
  have hstable : (prefixWord ++ tailWord_2862696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862696).length < 2 ^ (prefixWord ++ tailWord_2862696).sum := by decide
  have hdescent : baseEnd_2862696 < baseStart_2862696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862705 : List Nat := [1, 2, 2, 2, 1, 1, 1, 2, 5, 6]
def baseStart_2862705 : Nat := 118140960795 + 2862705 * 2 ^ 59
def prefixEnd_2862705 : Nat := 4983230072969 + 3 ^ 40 * 2862705 * 2
def baseEnd_2862705 : Nat := 489981212343109129074055

theorem tailTrace_2862705 : CollatzResearch.WordTrace tailWord_2862705 prefixEnd_2862705 489981212343109129074055 := by
  unfold tailWord_2862705
  simp only [CollatzResearch.WordTrace]
  refine ⟨104411429093916170934909569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69607619395944113956606379 104411429093916170934909569)
  ·
    refine ⟨78308571820437128201182177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104411429093916170934909569 78308571820437128201182177)
    ·
      refine ⟨58731428865327846150886633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78308571820437128201182177 58731428865327846150886633)
      ·
        refine ⟨44048571648995884613164975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58731428865327846150886633 44048571648995884613164975)
        ·
          refine ⟨66072857473493826919747463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44048571648995884613164975 66072857473493826919747463)
          ·
            refine ⟨99109286210240740379621195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66072857473493826919747463 99109286210240740379621195)
            ·
              refine ⟨148663929315361110569431793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99109286210240740379621195 148663929315361110569431793)
              ·
                refine ⟨111497946986520832927073845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148663929315361110569431793 111497946986520832927073845)
                ·
                  refine ⟨10452932529986328086913173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 111497946986520832927073845 10452932529986328086913173)
                  ·
                    refine ⟨489981212343109129074055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10452932529986328086913173 489981212343109129074055)
                    ·
                      rfl

theorem cell23_2862705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 5, 6].length) (baseStart_2862705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2862705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2862705 prefixEnd_2862705 := by exact prefixLift 2862705
  have htrace : WordTrace (prefixWord ++ tailWord_2862705) baseStart_2862705 baseEnd_2862705 := by
    simpa [prefixWord, tailWord_2862705, baseEnd_2862705] using wordTrace_append hprefix tailTrace_2862705
  have hstable : (prefixWord ++ tailWord_2862705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862705).length < 2 ^ (prefixWord ++ tailWord_2862705).sum := by decide
  have hdescent : baseEnd_2862705 < baseStart_2862705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862709 : List Nat := [1, 3, 4, 2, 1, 2, 1, 1, 3, 5]
def baseStart_2862709 : Nat := 118140960795 + 2862709 * 2 ^ 59
def prefixEnd_2862709 : Nat := 4983230072969 + 3 ^ 40 * 2862709 * 2
def baseEnd_2862709 : Nat := 489981896983981790524049

theorem tailTrace_2862709 : CollatzResearch.WordTrace tailWord_2862709 prefixEnd_2862709 489981896983981790524049 := by
  unfold tailWord_2862709
  simp only [CollatzResearch.WordTrace]
  refine ⟨104411574985901679618055181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69607716657267786412036787 104411574985901679618055181)
  ·
    refine ⟨39154340619713129856770693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104411574985901679618055181 39154340619713129856770693)
    ·
      refine ⟨7341438866196211848144505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39154340619713129856770693 7341438866196211848144505)
      ·
        refine ⟨5506079149647158886108379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7341438866196211848144505 5506079149647158886108379)
        ·
          refine ⟨8259118724470738329162569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5506079149647158886108379 8259118724470738329162569)
          ·
            refine ⟨6194339043353053746871927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8259118724470738329162569 6194339043353053746871927)
            ·
              refine ⟨9291508565029580620307891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6194339043353053746871927 9291508565029580620307891)
              ·
                refine ⟨13937262847544370930461837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9291508565029580620307891 13937262847544370930461837)
                ·
                  refine ⟨5226473567829139098923189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13937262847544370930461837 5226473567829139098923189)
                  ·
                    refine ⟨489981896983981790524049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5226473567829139098923189 489981896983981790524049)
                    ·
                      rfl

theorem cell23_2862709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_2862709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2862709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2862709 prefixEnd_2862709 := by exact prefixLift 2862709
  have htrace : WordTrace (prefixWord ++ tailWord_2862709) baseStart_2862709 baseEnd_2862709 := by
    simpa [prefixWord, tailWord_2862709, baseEnd_2862709] using wordTrace_append hprefix tailTrace_2862709
  have hstable : (prefixWord ++ tailWord_2862709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862709).length < 2 ^ (prefixWord ++ tailWord_2862709).sum := by decide
  have hdescent : baseEnd_2862709 < baseStart_2862709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862740 : List Nat := [2, 4, 2, 2, 2, 1, 1, 4, 1, 1, 3]
def baseStart_2862740 : Nat := 118140960795 + 2862740 * 2 ^ 59
def prefixEnd_2862740 : Nat := 4983230072969 + 3 ^ 40 * 2862740 * 2
def baseEnd_2862740 : Nat := 1469961608852234750284505

theorem tailTrace_2862740 : CollatzResearch.WordTrace tailWord_2862740 prefixEnd_2862740 1469961608852234750284505 := by
  unfold tailWord_2862740
  simp only [CollatzResearch.WordTrace]
  refine ⟨52206352824394685956216837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69608470432526247941622449 52206352824394685956216837)
  ·
    refine ⟨9788691154574003616790657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52206352824394685956216837 9788691154574003616790657)
    ·
      refine ⟨7341518365930502712592993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9788691154574003616790657 7341518365930502712592993)
      ·
        refine ⟨5506138774447877034444745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7341518365930502712592993 5506138774447877034444745)
        ·
          refine ⟨4129604080835907775833559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5506138774447877034444745 4129604080835907775833559)
          ·
            refine ⟨6194406121253861663750339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4129604080835907775833559 6194406121253861663750339)
            ·
              refine ⟨9291609181880792495625509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6194406121253861663750339 9291609181880792495625509)
              ·
                refine ⟨1742176721602648592929783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9291609181880792495625509 1742176721602648592929783)
                ·
                  refine ⟨2613265082403972889394675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1742176721602648592929783 2613265082403972889394675)
                  ·
                    refine ⟨3919897623605959334092013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2613265082403972889394675 3919897623605959334092013)
                    ·
                      refine ⟨1469961608852234750284505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3919897623605959334092013 1469961608852234750284505)
                      ·
                        rfl

theorem cell23_2862740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_2862740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2862740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2862740 prefixEnd_2862740 := by exact prefixLift 2862740
  have htrace : WordTrace (prefixWord ++ tailWord_2862740) baseStart_2862740 baseEnd_2862740 := by
    simpa [prefixWord, tailWord_2862740, baseEnd_2862740] using wordTrace_append hprefix tailTrace_2862740
  have hstable : (prefixWord ++ tailWord_2862740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862740).length < 2 ^ (prefixWord ++ tailWord_2862740).sum := by decide
  have hdescent : baseEnd_2862740 < baseStart_2862740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862745 : List Nat := [1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 7]
def baseStart_2862745 : Nat := 118140960795 + 2862745 * 2 ^ 59
def prefixEnd_2862745 : Nat := 4983230072969 + 3 ^ 40 * 2862745 * 2
def baseEnd_2862745 : Nat := 1469964176255507230721981

theorem tailTrace_2862745 : CollatzResearch.WordTrace tailWord_2862745 prefixEnd_2862745 1469964176255507230721981 := by
  unfold tailWord_2862745
  simp only [CollatzResearch.WordTrace]
  refine ⟨104412888013771257766365689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69608592009180838510910459 104412888013771257766365689)
  ·
    refine ⟨78309666010328443324774267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104412888013771257766365689 78309666010328443324774267)
    ·
      refine ⟨117464499015492664987161401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78309666010328443324774267 117464499015492664987161401)
      ·
        refine ⟨88098374261619498740371051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117464499015492664987161401 88098374261619498740371051)
        ·
          refine ⟨132147561392429248110556577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88098374261619498740371051 132147561392429248110556577)
          ·
            refine ⟨99110671044321936082917433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132147561392429248110556577 99110671044321936082917433)
            ·
              refine ⟨74333003283241452062188075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99110671044321936082917433 74333003283241452062188075)
              ·
                refine ⟨111499504924862178093282113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74333003283241452062188075 111499504924862178093282113)
                ·
                  refine ⟨83624628693646633569961585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111499504924862178093282113 83624628693646633569961585)
                  ·
                    refine ⟨62718471520234975177471189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 83624628693646633569961585 62718471520234975177471189)
                    ·
                      refine ⟨1469964176255507230721981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 62718471520234975177471189 1469964176255507230721981)
                      ·
                        rfl

theorem cell23_2862745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 7].length) (baseStart_2862745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2862745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2862745 prefixEnd_2862745 := by exact prefixLift 2862745
  have htrace : WordTrace (prefixWord ++ tailWord_2862745) baseStart_2862745 baseEnd_2862745 := by
    simpa [prefixWord, tailWord_2862745, baseEnd_2862745] using wordTrace_append hprefix tailTrace_2862745
  have hstable : (prefixWord ++ tailWord_2862745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862745).length < 2 ^ (prefixWord ++ tailWord_2862745).sum := by decide
  have hdescent : baseEnd_2862745 < baseStart_2862745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862752 : List Nat := [2, 1, 1, 4, 3, 1, 3, 8]
def baseStart_2862752 : Nat := 118140960795 + 2862752 * 2 ^ 59
def prefixEnd_2862752 : Nat := 4983230072969 + 3 ^ 40 * 2862752 * 2
def baseEnd_2862752 : Nat := 54443250763706989012387

theorem tailTrace_2862752 : CollatzResearch.WordTrace tailWord_2862752 prefixEnd_2862752 54443250763706989012387 := by
  unfold tailWord_2862752
  simp only [CollatzResearch.WordTrace]
  refine ⟨52206571662372948980935255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69608762216497265307913673 52206571662372948980935255)
  ·
    refine ⟨78309857493559423471402883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52206571662372948980935255 78309857493559423471402883)
    ·
      refine ⟨117464786240339135207104325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78309857493559423471402883 117464786240339135207104325)
      ·
        refine ⟨22024647420063587851332061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 117464786240339135207104325 22024647420063587851332061)
        ·
          refine ⟨8259242782523845444249523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22024647420063587851332061 8259242782523845444249523)
          ·
            refine ⟨12388864173785768166374285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8259242782523845444249523 12388864173785768166374285)
            ·
              refine ⟨4645824065169663062390357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12388864173785768166374285 4645824065169663062390357)
              ·
                refine ⟨54443250763706989012387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4645824065169663062390357 54443250763706989012387)
                ·
                  rfl

theorem cell23_2862752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 8].length) (baseStart_2862752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2862752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2862752 prefixEnd_2862752 := by exact prefixLift 2862752
  have htrace : WordTrace (prefixWord ++ tailWord_2862752) baseStart_2862752 baseEnd_2862752 := by
    simpa [prefixWord, tailWord_2862752, baseEnd_2862752] using wordTrace_append hprefix tailTrace_2862752
  have hstable : (prefixWord ++ tailWord_2862752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862752).length < 2 ^ (prefixWord ++ tailWord_2862752).sum := by decide
  have hdescent : baseEnd_2862752 < baseStart_2862752 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862780 : List Nat := [2, 2, 2, 3, 1, 3, 2, 3, 1, 2, 2]
def baseStart_2862780 : Nat := 118140960795 + 2862780 * 2 ^ 59
def prefixEnd_2862780 : Nat := 4983230072969 + 3 ^ 40 * 2862780 * 2
def baseEnd_2862780 : Nat := 1469982148078414593784321

theorem tailTrace_2862780 : CollatzResearch.WordTrace tailWord_2862780 prefixEnd_2862780 1469982148078414593784321 := by
  unfold tailWord_2862780
  simp only [CollatzResearch.WordTrace]
  refine ⟨52207082284322229371944897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69609443045762972495926529 52207082284322229371944897)
  ·
    refine ⟨39155311713241672028958673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52207082284322229371944897 39155311713241672028958673)
    ·
      refine ⟨29366483784931254021719005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39155311713241672028958673 29366483784931254021719005)
      ·
        refine ⟨11012431419349220258144627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29366483784931254021719005 11012431419349220258144627)
        ·
          refine ⟨16518647129023830387216941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11012431419349220258144627 16518647129023830387216941)
          ·
            refine ⟨6194492673383936395206353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16518647129023830387216941 6194492673383936395206353)
            ·
              refine ⟨4645869505037952296404765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6194492673383936395206353 4645869505037952296404765)
              ·
                refine ⟨1742201064389232111151787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4645869505037952296404765 1742201064389232111151787)
                ·
                  refine ⟨2613301596583848166727681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1742201064389232111151787 2613301596583848166727681)
                  ·
                    refine ⟨1959976197437886125045761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2613301596583848166727681 1959976197437886125045761)
                    ·
                      refine ⟨1469982148078414593784321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1959976197437886125045761 1469982148078414593784321)
                      ·
                        rfl

theorem cell23_2862780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 3, 1, 2, 2].length) (baseStart_2862780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2862780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2862780 prefixEnd_2862780 := by exact prefixLift 2862780
  have htrace : WordTrace (prefixWord ++ tailWord_2862780) baseStart_2862780 baseEnd_2862780 := by
    simpa [prefixWord, tailWord_2862780, baseEnd_2862780] using wordTrace_append hprefix tailTrace_2862780
  have hstable : (prefixWord ++ tailWord_2862780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862780).length < 2 ^ (prefixWord ++ tailWord_2862780).sum := by decide
  have hdescent : baseEnd_2862780 < baseStart_2862780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862790 : List Nat := [6, 1, 2, 1, 1, 1, 3, 2, 2, 4]
def baseStart_2862790 : Nat := 118140960795 + 2862790 * 2 ^ 59
def prefixEnd_2862790 : Nat := 4983230072969 + 3 ^ 40 * 2862790 * 2
def baseEnd_2862790 : Nat := 489995760961653184886425

theorem tailTrace_2862790 : CollatzResearch.WordTrace tailWord_2862790 prefixEnd_2862790 489995760961653184886425 := by
  unfold tailWord_2862790
  simp only [CollatzResearch.WordTrace]
  refine ⟨3262954040581507201617307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 69609686199072153634502549 3262954040581507201617307)
  ·
    refine ⟨4894431060872260802425961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3262954040581507201617307 4894431060872260802425961)
    ·
      refine ⟨3670823295654195601819471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4894431060872260802425961 3670823295654195601819471)
      ·
        refine ⟨5506234943481293402729207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3670823295654195601819471 5506234943481293402729207)
        ·
          refine ⟨8259352415221940104093811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5506234943481293402729207 8259352415221940104093811)
          ·
            refine ⟨12389028622832910156140717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8259352415221940104093811 12389028622832910156140717)
            ·
              refine ⟨4645885733562341308552769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12389028622832910156140717 4645885733562341308552769)
              ·
                refine ⟨3484414300171755981414577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4645885733562341308552769 3484414300171755981414577)
                ·
                  refine ⟨2613310725128816986060933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3484414300171755981414577 2613310725128816986060933)
                  ·
                    refine ⟨489995760961653184886425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2613310725128816986060933 489995760961653184886425)
                    ·
                      rfl

theorem cell23_2862790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_2862790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2862790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2862790 prefixEnd_2862790 := by exact prefixLift 2862790
  have htrace : WordTrace (prefixWord ++ tailWord_2862790) baseStart_2862790 baseEnd_2862790 := by
    simpa [prefixWord, tailWord_2862790, baseEnd_2862790] using wordTrace_append hprefix tailTrace_2862790
  have hstable : (prefixWord ++ tailWord_2862790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862790).length < 2 ^ (prefixWord ++ tailWord_2862790).sum := by decide
  have hdescent : baseEnd_2862790 < baseStart_2862790 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862797 : List Nat := [1, 6, 2, 1, 1, 1, 2, 4, 1, 2, 2]
def baseStart_2862797 : Nat := 118140960795 + 2862797 * 2 ^ 59
def prefixEnd_2862797 : Nat := 4983230072969 + 3 ^ 40 * 2862797 * 2
def baseEnd_2862797 : Nat := 1469990877249541027271743

theorem tailTrace_2862797 : CollatzResearch.WordTrace tailWord_2862797 prefixEnd_2862797 1469990877249541027271743 := by
  unfold tailWord_2862797
  simp only [CollatzResearch.WordTrace]
  refine ⟨104414784609582870647258645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69609856406388580431505763 104414784609582870647258645)
  ·
    refine ⟨4894443028574197061590249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 104414784609582870647258645 4894443028574197061590249)
    ·
      refine ⟨3670832271430647796192687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4894443028574197061590249 3670832271430647796192687)
      ·
        refine ⟨5506248407145971694289031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3670832271430647796192687 5506248407145971694289031)
        ·
          refine ⟨8259372610718957541433547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5506248407145971694289031 8259372610718957541433547)
          ·
            refine ⟨12389058916078436312150321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8259372610718957541433547 12389058916078436312150321)
            ·
              refine ⟨9291794187058827234112741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12389058916078436312150321 9291794187058827234112741)
              ·
                refine ⟨1742211410073530106396139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9291794187058827234112741 1742211410073530106396139)
                ·
                  refine ⟨2613317115110295159594209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1742211410073530106396139 2613317115110295159594209)
                  ·
                    refine ⟨1959987836332721369695657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2613317115110295159594209 1959987836332721369695657)
                    ·
                      refine ⟨1469990877249541027271743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1959987836332721369695657 1469990877249541027271743)
                      ·
                        rfl

theorem cell23_2862797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_2862797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2862797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2862797 prefixEnd_2862797 := by exact prefixLift 2862797
  have htrace : WordTrace (prefixWord ++ tailWord_2862797) baseStart_2862797 baseEnd_2862797 := by
    simpa [prefixWord, tailWord_2862797, baseEnd_2862797] using wordTrace_append hprefix tailTrace_2862797
  have hstable : (prefixWord ++ tailWord_2862797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862797).length < 2 ^ (prefixWord ++ tailWord_2862797).sum := by decide
  have hdescent : baseEnd_2862797 < baseStart_2862797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862832 : List Nat := [2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 4]
def baseStart_2862832 : Nat := 118140960795 + 2862832 * 2 ^ 59
def prefixEnd_2862832 : Nat := 4983230072969 + 3 ^ 40 * 2862832 * 2
def baseEnd_2862832 : Nat := 1470008849072448390334081

theorem tailTrace_2862832 : CollatzResearch.WordTrace tailWord_2862832 prefixEnd_2862832 1470008849072448390334081 := by
  unfold tailWord_2862832
  simp only [CollatzResearch.WordTrace]
  refine ⟨52208030582228035812391375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69610707442970714416521833 52208030582228035812391375)
  ·
    refine ⟨78312045873342053718587063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52208030582228035812391375 78312045873342053718587063)
    ·
      refine ⟨117468068810013080577880595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78312045873342053718587063 117468068810013080577880595)
      ·
        refine ⟨176202103215019620866820893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117468068810013080577880595 176202103215019620866820893)
        ·
          refine ⟨66075788705632357825057835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176202103215019620866820893 66075788705632357825057835)
          ·
            refine ⟨99113683058448536737586753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66075788705632357825057835 99113683058448536737586753)
            ·
              refine ⟨74335262293836402553190065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99113683058448536737586753 74335262293836402553190065)
              ·
                refine ⟨55751446720377301914892549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74335262293836402553190065 55751446720377301914892549)
                ·
                  refine ⟨10453396260070744109042353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55751446720377301914892549 10453396260070744109042353)
                  ·
                    refine ⟨7840047195053058081781765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10453396260070744109042353 7840047195053058081781765)
                    ·
                      refine ⟨1470008849072448390334081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7840047195053058081781765 1470008849072448390334081)
                      ·
                        rfl

theorem cell23_2862832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 4].length) (baseStart_2862832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2862832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2862832 prefixEnd_2862832 := by exact prefixLift 2862832
  have htrace : WordTrace (prefixWord ++ tailWord_2862832) baseStart_2862832 baseEnd_2862832 := by
    simpa [prefixWord, tailWord_2862832, baseEnd_2862832] using wordTrace_append hprefix tailTrace_2862832
  have hstable : (prefixWord ++ tailWord_2862832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862832).length < 2 ^ (prefixWord ++ tailWord_2862832).sum := by decide
  have hdescent : baseEnd_2862832 < baseStart_2862832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862859 : List Nat := [1, 1, 1, 1, 5, 1, 2, 6, 5]
def baseStart_2862859 : Nat := 118140960795 + 2862859 * 2 ^ 59
def prefixEnd_2862859 : Nat := 4983230072969 + 3 ^ 40 * 2862859 * 2
def baseEnd_2862859 : Nat := 163335857005568864966273

theorem tailTrace_2862859 : CollatzResearch.WordTrace tailWord_2862859 prefixEnd_2862859 163335857005568864966273 := by
  unfold tailWord_2862859
  simp only [CollatzResearch.WordTrace]
  refine ⟨104417045935358255236015631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69611363956905503490677087 104417045935358255236015631)
  ·
    refine ⟨156625568903037382854023447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104417045935358255236015631 156625568903037382854023447)
    ·
      refine ⟨234938353354556074281035171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156625568903037382854023447 234938353354556074281035171)
      ·
        refine ⟨352407530031834111421552757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234938353354556074281035171 352407530031834111421552757)
        ·
          refine ⟨33038205940484447945770571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 352407530031834111421552757 33038205940484447945770571)
          ·
            refine ⟨49557308910726671918655857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33038205940484447945770571 49557308910726671918655857)
            ·
              refine ⟨37167981683045003938991893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49557308910726671918655857 37167981683045003938991893)
              ·
                refine ⟨1742249141392734559640245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 37167981683045003938991893 1742249141392734559640245)
                ·
                  refine ⟨163335857005568864966273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1742249141392734559640245 163335857005568864966273)
                  ·
                    rfl

theorem cell23_2862859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 6, 5].length) (baseStart_2862859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2862859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2862859 prefixEnd_2862859 := by exact prefixLift 2862859
  have htrace : WordTrace (prefixWord ++ tailWord_2862859) baseStart_2862859 baseEnd_2862859 := by
    simpa [prefixWord, tailWord_2862859, baseEnd_2862859] using wordTrace_append hprefix tailTrace_2862859
  have hstable : (prefixWord ++ tailWord_2862859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862859).length < 2 ^ (prefixWord ++ tailWord_2862859).sum := by decide
  have hdescent : baseEnd_2862859 < baseStart_2862859 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862872 : List Nat := [2, 1, 2, 3, 1, 1, 2, 1, 3, 7]
def baseStart_2862872 : Nat := 118140960795 + 2862872 * 2 ^ 59
def prefixEnd_2862872 : Nat := 4983230072969 + 3 ^ 40 * 2862872 * 2
def baseEnd_2862872 : Nat := 490009796099542744611299

theorem tailTrace_2862872 : CollatzResearch.WordTrace tailWord_2862872 prefixEnd_2862872 490009796099542744611299 := by
  unfold tailWord_2862872
  simp only [CollatzResearch.WordTrace]
  refine ⟨52208760042155579228119435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69611680056207438970825913 52208760042155579228119435)
  ·
    refine ⟨78313140063233368842179153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52208760042155579228119435 78313140063233368842179153)
    ·
      refine ⟨58734855047425026631634365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78313140063233368842179153 58734855047425026631634365)
      ·
        refine ⟨22025570642784384986862887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58734855047425026631634365 22025570642784384986862887)
        ·
          refine ⟨33038355964176577480294331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22025570642784384986862887 33038355964176577480294331)
          ·
            refine ⟨49557533946264866220441497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33038355964176577480294331 49557533946264866220441497)
            ·
              refine ⟨37168150459698649665331123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49557533946264866220441497 37168150459698649665331123)
              ·
                refine ⟨55752225689547974497996685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37168150459698649665331123 55752225689547974497996685)
                ·
                  refine ⟨20907084633580490436748757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55752225689547974497996685 20907084633580490436748757)
                  ·
                    refine ⟨490009796099542744611299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20907084633580490436748757 490009796099542744611299)
                    ·
                      rfl

theorem cell23_2862872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 3, 7].length) (baseStart_2862872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2862872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2862872 prefixEnd_2862872 := by exact prefixLift 2862872
  have htrace : WordTrace (prefixWord ++ tailWord_2862872) baseStart_2862872 baseEnd_2862872 := by
    simpa [prefixWord, tailWord_2862872, baseEnd_2862872] using wordTrace_append hprefix tailTrace_2862872
  have hstable : (prefixWord ++ tailWord_2862872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862872).length < 2 ^ (prefixWord ++ tailWord_2862872).sum := by decide
  have hdescent : baseEnd_2862872 < baseStart_2862872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862910 : List Nat := [4, 2, 1, 2, 2, 3, 2, 2, 5]
def baseStart_2862910 : Nat := 118140960795 + 2862910 * 2 ^ 59
def prefixEnd_2862910 : Nat := 4983230072969 + 3 ^ 40 * 2862910 * 2
def baseEnd_2862910 : Nat := 163338766729277676128747

theorem tailTrace_2862910 : CollatzResearch.WordTrace tailWord_2862910 prefixEnd_2862910 163338766729277676128747 := by
  unfold tailWord_2862910
  simp only [CollatzResearch.WordTrace]
  refine ⟨13052363257271686368265273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69612604038782327297414789 13052363257271686368265273)
  ·
    refine ⟨9789272442953764776198955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13052363257271686368265273 9789272442953764776198955)
    ·
      refine ⟨14683908664430647164298433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9789272442953764776198955 14683908664430647164298433)
      ·
        refine ⟨11012931498322985373223825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14683908664430647164298433 11012931498322985373223825)
        ·
          refine ⟨8259698623742239029917869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11012931498322985373223825 8259698623742239029917869)
          ·
            refine ⟨3097386983903339636219201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8259698623742239029917869 3097386983903339636219201)
            ·
              refine ⟨2323040237927504727164401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3097386983903339636219201 2323040237927504727164401)
              ·
                refine ⟨1742280178445628545373301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2323040237927504727164401 1742280178445628545373301)
                ·
                  refine ⟨163338766729277676128747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1742280178445628545373301 163338766729277676128747)
                  ·
                    rfl

theorem cell23_2862910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 2, 2, 5].length) (baseStart_2862910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2862910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2862910 prefixEnd_2862910 := by exact prefixLift 2862910
  have htrace : WordTrace (prefixWord ++ tailWord_2862910) baseStart_2862910 baseEnd_2862910 := by
    simpa [prefixWord, tailWord_2862910, baseEnd_2862910] using wordTrace_append hprefix tailTrace_2862910
  have hstable : (prefixWord ++ tailWord_2862910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862910).length < 2 ^ (prefixWord ++ tailWord_2862910).sum := by decide
  have hdescent : baseEnd_2862910 < baseStart_2862910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862940 : List Nat := [2, 2, 4, 2, 3, 1, 1, 1, 2, 5]
def baseStart_2862940 : Nat := 118140960795 + 2862940 * 2 ^ 59
def prefixEnd_2862940 : Nat := 4983230072969 + 3 ^ 40 * 2862940 * 2
def baseEnd_2862940 : Nat := 490021434994377989261195

theorem tailTrace_2862940 : CollatzResearch.WordTrace tailWord_2862940 prefixEnd_2862940 490021434994377989261195 := by
  unfold tailWord_2862940
  simp only [CollatzResearch.WordTrace]
  refine ⟨52210000124032403034857137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69613333498709870713142849 52210000124032403034857137)
  ·
    refine ⟨39157500093024302276142853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52210000124032403034857137 39157500093024302276142853)
    ·
      refine ⟨7342031267442056676776785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39157500093024302276142853 7342031267442056676776785)
      ·
        refine ⟨5506523450581542507582589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7342031267442056676776785 5506523450581542507582589)
        ·
          refine ⟨2064946293968078440343471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5506523450581542507582589 2064946293968078440343471)
          ·
            refine ⟨3097419440952117660515207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2064946293968078440343471 3097419440952117660515207)
            ·
              refine ⟨4646129161428176490772811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3097419440952117660515207 4646129161428176490772811)
              ·
                refine ⟨6969193742142264736159217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4646129161428176490772811 6969193742142264736159217)
                ·
                  refine ⟨5226895306606698552119413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6969193742142264736159217 5226895306606698552119413)
                  ·
                    refine ⟨490021434994377989261195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5226895306606698552119413 490021434994377989261195)
                    ·
                      rfl

theorem cell23_2862940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_2862940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2862940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2862940 prefixEnd_2862940 := by exact prefixLift 2862940
  have htrace : WordTrace (prefixWord ++ tailWord_2862940) baseStart_2862940 baseEnd_2862940 := by
    simpa [prefixWord, tailWord_2862940, baseEnd_2862940] using wordTrace_append hprefix tailTrace_2862940
  have hstable : (prefixWord ++ tailWord_2862940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862940).length < 2 ^ (prefixWord ++ tailWord_2862940).sum := by decide
  have hdescent : baseEnd_2862940 < baseStart_2862940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2862983 : List Nat := [1, 1, 4, 2, 4, 1, 3, 1, 6]
def baseStart_2862983 : Nat := 118140960795 + 2862983 * 2 ^ 59
def prefixEnd_2862983 : Nat := 4983230072969 + 3 ^ 40 * 2862983 * 2
def baseEnd_2862983 : Nat := 163342931627919699949543

theorem tailTrace_2862983 : CollatzResearch.WordTrace tailWord_2862983 prefixEnd_2862983 163342931627919699949543 := by
  unfold tailWord_2862983
  simp only [CollatzResearch.WordTrace]
  refine ⟨104421568586909024413529603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69614379057939349609019735 104421568586909024413529603)
  ·
    refine ⟨156632352880363536620294405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104421568586909024413529603 156632352880363536620294405)
    ·
      refine ⟨29368566165068163116305201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 156632352880363536620294405 29368566165068163116305201)
      ·
        refine ⟨22026424623801122337228901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29368566165068163116305201 22026424623801122337228901)
        ·
          refine ⟨4129954616962710438230419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22026424623801122337228901 4129954616962710438230419)
          ·
            refine ⟨6194931925444065657345629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4129954616962710438230419 6194931925444065657345629)
            ·
              refine ⟨2323099472041524621504611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6194931925444065657345629 2323099472041524621504611)
              ·
                refine ⟨3484649208062286932256917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2323099472041524621504611 3484649208062286932256917)
                ·
                  refine ⟨163342931627919699949543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3484649208062286932256917 163342931627919699949543)
                  ·
                    rfl

theorem cell23_2862983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 3, 1, 6].length) (baseStart_2862983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2862983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2862983 prefixEnd_2862983 := by exact prefixLift 2862983
  have htrace : WordTrace (prefixWord ++ tailWord_2862983) baseStart_2862983 baseEnd_2862983 := by
    simpa [prefixWord, tailWord_2862983, baseEnd_2862983] using wordTrace_append hprefix tailTrace_2862983
  have hstable : (prefixWord ++ tailWord_2862983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2862983).length < 2 ^ (prefixWord ++ tailWord_2862983).sum := by decide
  have hdescent : baseEnd_2862983 < baseStart_2862983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2862983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863039 : List Nat := [1, 1, 2, 2, 2, 1, 6, 8]
def baseStart_2863039 : Nat := 118140960795 + 2863039 * 2 ^ 59
def prefixEnd_2863039 : Nat := 4983230072969 + 3 ^ 40 * 2863039 * 2
def baseEnd_2863039 : Nat := 54448708872886262238727

theorem tailTrace_2863039 : CollatzResearch.WordTrace tailWord_2863039 prefixEnd_2863039 54448708872886262238727 := by
  unfold tailWord_2863039
  simp only [CollatzResearch.WordTrace]
  refine ⟨104423611074706145977568171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69615740716470763985045447 104423611074706145977568171)
  ·
    refine ⟨156635416612059218966352257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104423611074706145977568171 156635416612059218966352257)
    ·
      refine ⟨117476562459044414224764193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156635416612059218966352257 117476562459044414224764193)
      ·
        refine ⟨88107421844283310668573145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117476562459044414224764193 88107421844283310668573145)
        ·
          refine ⟨66080566383212483001429859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88107421844283310668573145 66080566383212483001429859)
          ·
            refine ⟨99120849574818724502144789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66080566383212483001429859 99120849574818724502144789)
            ·
              refine ⟨4646289823819627711038037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 99120849574818724502144789 4646289823819627711038037)
              ·
                refine ⟨54448708872886262238727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4646289823819627711038037 54448708872886262238727)
                ·
                  rfl

theorem cell23_2863039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 8].length) (baseStart_2863039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2863039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2863039 prefixEnd_2863039 := by exact prefixLift 2863039
  have htrace : WordTrace (prefixWord ++ tailWord_2863039) baseStart_2863039 baseEnd_2863039 := by
    simpa [prefixWord, tailWord_2863039, baseEnd_2863039] using wordTrace_append hprefix tailTrace_2863039
  have hstable : (prefixWord ++ tailWord_2863039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863039).length < 2 ^ (prefixWord ++ tailWord_2863039).sum := by decide
  have hdescent : baseEnd_2863039 < baseStart_2863039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863086 : List Nat := [4, 1, 2, 1, 3, 1, 1, 1, 2, 7]
def baseStart_2863086 : Nat := 118140960795 + 2863086 * 2 ^ 59
def prefixEnd_2863086 : Nat := 4983230072969 + 3 ^ 40 * 2863086 * 2
def baseEnd_2863086 : Nat := 490046424386230132185971

theorem tailTrace_2863086 : CollatzResearch.WordTrace tailWord_2863086 prefixEnd_2863086 490046424386230132185971 := by
  unfold tailWord_2863086
  simp only [CollatzResearch.WordTrace]
  refine ⟨13053165663191984125566139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69616883537023915336352741 13053165663191984125566139)
  ·
    refine ⟨19579748494787976188349209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13053165663191984125566139 19579748494787976188349209)
    ·
      refine ⟨14684811371090982141261907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19579748494787976188349209 14684811371090982141261907)
      ·
        refine ⟨22027217056636473211892861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14684811371090982141261907 22027217056636473211892861)
        ·
          refine ⟨8260206396238677454459823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22027217056636473211892861 8260206396238677454459823)
          ·
            refine ⟨12390309594358016181689735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8260206396238677454459823 12390309594358016181689735)
            ·
              refine ⟨18585464391537024272534603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12390309594358016181689735 18585464391537024272534603)
              ·
                refine ⟨27878196587305536408801905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18585464391537024272534603 27878196587305536408801905)
                ·
                  refine ⟨20908647440479152306601429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27878196587305536408801905 20908647440479152306601429)
                  ·
                    refine ⟨490046424386230132185971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20908647440479152306601429 490046424386230132185971)
                    ·
                      rfl

theorem cell23_2863086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_2863086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2863086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2863086 prefixEnd_2863086 := by exact prefixLift 2863086
  have htrace : WordTrace (prefixWord ++ tailWord_2863086) baseStart_2863086 baseEnd_2863086 := by
    simpa [prefixWord, tailWord_2863086, baseEnd_2863086] using wordTrace_append hprefix tailTrace_2863086
  have hstable : (prefixWord ++ tailWord_2863086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863086).length < 2 ^ (prefixWord ++ tailWord_2863086).sum := by decide
  have hdescent : baseEnd_2863086 < baseStart_2863086 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863099 : List Nat := [1, 1, 1, 1, 1, 3, 5, 1, 1, 8]
def baseStart_2863099 : Nat := 118140960795 + 2863099 * 2 ^ 59
def prefixEnd_2863099 : Nat := 4983230072969 + 3 ^ 40 * 2863099 * 2
def baseEnd_2863099 : Nat := 490048649469066281898451

theorem tailTrace_2863099 : CollatzResearch.WordTrace tailWord_2863099 prefixEnd_2863099 490048649469066281898451 := by
  unfold tailWord_2863099
  simp only [CollatzResearch.WordTrace]
  refine ⟨104425799454488776224752351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69617199636325850816501567 104425799454488776224752351)
  ·
    refine ⟨156638699181733164337128527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104425799454488776224752351 156638699181733164337128527)
    ·
      refine ⟨234958048772599746505692791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156638699181733164337128527 234958048772599746505692791)
      ·
        refine ⟨352437073158899619758539187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234958048772599746505692791 352437073158899619758539187)
        ·
          refine ⟨528655609738349429637808781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 352437073158899619758539187 528655609738349429637808781)
          ·
            refine ⟨198245853651881036114178293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 528655609738349429637808781 198245853651881036114178293)
            ·
              refine ⟨18585548779863847135704215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 198245853651881036114178293 18585548779863847135704215)
              ·
                refine ⟨27878323169795770703556323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18585548779863847135704215 27878323169795770703556323)
                ·
                  refine ⟨41817484754693656055334485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27878323169795770703556323 41817484754693656055334485)
                  ·
                    refine ⟨490048649469066281898451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 41817484754693656055334485 490048649469066281898451)
                    ·
                      rfl

theorem cell23_2863099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 8].length) (baseStart_2863099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2863099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2863099 prefixEnd_2863099 := by exact prefixLift 2863099
  have htrace : WordTrace (prefixWord ++ tailWord_2863099) baseStart_2863099 baseEnd_2863099 := by
    simpa [prefixWord, tailWord_2863099, baseEnd_2863099] using wordTrace_append hprefix tailTrace_2863099
  have hstable : (prefixWord ++ tailWord_2863099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863099).length < 2 ^ (prefixWord ++ tailWord_2863099).sum := by decide
  have hdescent : baseEnd_2863099 < baseStart_2863099 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863123 : List Nat := [1, 1, 1, 2, 1, 4, 4, 2, 1, 4, 2]
def baseStart_2863123 : Nat := 118140960795 + 2863123 * 2 ^ 59
def prefixEnd_2863123 : Nat := 4983230072969 + 3 ^ 40 * 2863123 * 2
def baseEnd_2863123 : Nat := 1470158271942906751795243

theorem tailTrace_2863123 : CollatzResearch.WordTrace tailWord_2863123 prefixEnd_2863123 1470158271942906751795243 := by
  unfold tailWord_2863123
  simp only [CollatzResearch.WordTrace]
  refine ⟨104426674806401828323626023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69617783204267885549084015 104426674806401828323626023)
  ·
    refine ⟨156640012209602742485439035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104426674806401828323626023 156640012209602742485439035)
    ·
      refine ⟨234960018314404113728158553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156640012209602742485439035 234960018314404113728158553)
      ·
        refine ⟨176220013735803085296118915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234960018314404113728158553 176220013735803085296118915)
        ·
          refine ⟨264330020603704627944178373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176220013735803085296118915 264330020603704627944178373)
          ·
            refine ⟨49561878863194617739533445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 264330020603704627944178373 49561878863194617739533445)
            ·
              refine ⟨9292852286848990826162521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49561878863194617739533445 9292852286848990826162521)
              ·
                refine ⟨6969639215136743119621891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9292852286848990826162521 6969639215136743119621891)
                ·
                  refine ⟨10454458822705114679432837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6969639215136743119621891 10454458822705114679432837)
                  ·
                    refine ⟨1960211029257209002393657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10454458822705114679432837 1960211029257209002393657)
                    ·
                      refine ⟨1470158271942906751795243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1960211029257209002393657 1470158271942906751795243)
                      ·
                        rfl

theorem cell23_2863123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 2, 1, 4, 2].length) (baseStart_2863123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2863123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2863123 prefixEnd_2863123 := by exact prefixLift 2863123
  have htrace : WordTrace (prefixWord ++ tailWord_2863123) baseStart_2863123 baseEnd_2863123 := by
    simpa [prefixWord, tailWord_2863123, baseEnd_2863123] using wordTrace_append hprefix tailTrace_2863123
  have hstable : (prefixWord ++ tailWord_2863123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863123).length < 2 ^ (prefixWord ++ tailWord_2863123).sum := by decide
  have hdescent : baseEnd_2863123 < baseStart_2863123 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863127 : List Nat := [1, 1, 3, 5, 2, 1, 1, 3, 1, 3, 2]
def baseStart_2863127 : Nat := 118140960795 + 2863127 * 2 ^ 59
def prefixEnd_2863127 : Nat := 4983230072969 + 3 ^ 40 * 2863127 * 2
def baseEnd_2863127 : Nat := 1470160325865524736145225

theorem tailTrace_2863127 : CollatzResearch.WordTrace tailWord_2863127 prefixEnd_2863127 1470160325865524736145225 := by
  unfold tailWord_2863127
  simp only [CollatzResearch.WordTrace]
  refine ⟨104426820698387337006771635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69617880465591558004514423 104426820698387337006771635)
  ·
    refine ⟨156640231047581005510157453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104426820698387337006771635 156640231047581005510157453)
    ·
      refine ⟨58740086642842877066309045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156640231047581005510157453 58740086642842877066309045)
      ·
        refine ⟨5506883122766519724966473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58740086642842877066309045 5506883122766519724966473)
        ·
          refine ⟨4130162342074889793724855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5506883122766519724966473 4130162342074889793724855)
          ·
            refine ⟨6195243513112334690587283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4130162342074889793724855 6195243513112334690587283)
            ·
              refine ⟨9292865269668502035880925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6195243513112334690587283 9292865269668502035880925)
              ·
                refine ⟨3484824476125688263455347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9292865269668502035880925 3484824476125688263455347)
                ·
                  refine ⟨5227236714188532395183021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3484824476125688263455347 5227236714188532395183021)
                  ·
                    refine ⟨1960213767820699648193633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5227236714188532395183021 1960213767820699648193633)
                    ·
                      refine ⟨1470160325865524736145225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1960213767820699648193633 1470160325865524736145225)
                      ·
                        rfl

theorem cell23_2863127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_2863127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2863127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2863127 prefixEnd_2863127 := by exact prefixLift 2863127
  have htrace : WordTrace (prefixWord ++ tailWord_2863127) baseStart_2863127 baseEnd_2863127 := by
    simpa [prefixWord, tailWord_2863127, baseEnd_2863127] using wordTrace_append hprefix tailTrace_2863127
  have hstable : (prefixWord ++ tailWord_2863127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863127).length < 2 ^ (prefixWord ++ tailWord_2863127).sum := by decide
  have hdescent : baseEnd_2863127 < baseStart_2863127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863129 : List Nat := [1, 2, 1, 2, 1, 1, 3, 1, 11]
def baseStart_2863129 : Nat := 118140960795 + 2863129 * 2 ^ 59
def prefixEnd_2863129 : Nat := 4983230072969 + 3 ^ 40 * 2863129 * 2
def baseEnd_2863129 : Nat := 163351261425203747591135

theorem tailTrace_2863129 : CollatzResearch.WordTrace tailWord_2863129 prefixEnd_2863129 163351261425203747591135 := by
  unfold tailWord_2863129
  simp only [CollatzResearch.WordTrace]
  refine ⟨104426893644380091348344441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69617929096253394232229627 104426893644380091348344441)
  ·
    refine ⟨78320170233285068511258331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104426893644380091348344441 78320170233285068511258331)
    ·
      refine ⟨117480255349927602766887497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78320170233285068511258331 117480255349927602766887497)
      ·
        refine ⟨88110191512445702075165623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117480255349927602766887497 88110191512445702075165623)
        ·
          refine ⟨132165287268668553112748435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88110191512445702075165623 132165287268668553112748435)
          ·
            refine ⟨198247930903002829669122653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132165287268668553112748435 198247930903002829669122653)
            ·
              refine ⟨74342974088626061125920995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 198247930903002829669122653 74342974088626061125920995)
              ·
                refine ⟨111514461132939091688881493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74342974088626061125920995 111514461132939091688881493)
                ·
                  refine ⟨163351261425203747591135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 111514461132939091688881493 163351261425203747591135)
                  ·
                    rfl

theorem cell23_2863129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 11].length) (baseStart_2863129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2863129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2863129 prefixEnd_2863129 := by exact prefixLift 2863129
  have htrace : WordTrace (prefixWord ++ tailWord_2863129) baseStart_2863129 baseEnd_2863129 := by
    simpa [prefixWord, tailWord_2863129, baseEnd_2863129] using wordTrace_append hprefix tailTrace_2863129
  have hstable : (prefixWord ++ tailWord_2863129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863129).length < 2 ^ (prefixWord ++ tailWord_2863129).sum := by decide
  have hdescent : baseEnd_2863129 < baseStart_2863129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863213 : List Nat := [1, 5, 1, 1, 2, 1, 1, 2, 4, 1, 4]
def baseStart_2863213 : Nat := 118140960795 + 2863213 * 2 ^ 59
def prefixEnd_2863213 : Nat := 4983230072969 + 3 ^ 40 * 2863213 * 2
def baseEnd_2863213 : Nat := 1470204485201811399669829

theorem tailTrace_2863213 : CollatzResearch.WordTrace tailWord_2863213 prefixEnd_2863213 1470204485201811399669829 := by
  unfold tailWord_2863213
  simp only [CollatzResearch.WordTrace]
  refine ⟨104429957376075773694402293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69619971584050515796268195 104429957376075773694402293)
  ·
    refine ⟨9790308504007103783850215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 104429957376075773694402293 9790308504007103783850215)
    ·
      refine ⟨14685462756010655675775323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9790308504007103783850215 14685462756010655675775323)
      ·
        refine ⟨22028194134015983513662985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14685462756010655675775323 22028194134015983513662985)
        ·
          refine ⟨16521145600511987635247239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22028194134015983513662985 16521145600511987635247239)
          ·
            refine ⟨24781718400767981452870859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16521145600511987635247239 24781718400767981452870859)
            ·
              refine ⟨37172577601151972179306289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24781718400767981452870859 37172577601151972179306289)
              ·
                refine ⟨27879433200863979134479717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37172577601151972179306289 27879433200863979134479717)
                ·
                  refine ⟨5227393725161996087714947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27879433200863979134479717 5227393725161996087714947)
                  ·
                    refine ⟨7841090587742994131572421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5227393725161996087714947 7841090587742994131572421)
                    ·
                      refine ⟨1470204485201811399669829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7841090587742994131572421 1470204485201811399669829)
                      ·
                        rfl

theorem cell23_2863213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_2863213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2863213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2863213 prefixEnd_2863213 := by exact prefixLift 2863213
  have htrace : WordTrace (prefixWord ++ tailWord_2863213) baseStart_2863213 baseEnd_2863213 := by
    simpa [prefixWord, tailWord_2863213, baseEnd_2863213] using wordTrace_append hprefix tailTrace_2863213
  have hstable : (prefixWord ++ tailWord_2863213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863213).length < 2 ^ (prefixWord ++ tailWord_2863213).sum := by decide
  have hdescent : baseEnd_2863213 < baseStart_2863213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863250 : List Nat := [3, 2, 3, 1, 1, 1, 1, 4, 2, 2, 3]
def baseStart_2863250 : Nat := 118140960795 + 2863250 * 2 ^ 59
def prefixEnd_2863250 : Nat := 4983230072969 + 3 ^ 40 * 2863250 * 2
def baseEnd_2863250 : Nat := 1470223483986027754907159

theorem tailTrace_2863250 : CollatzResearch.WordTrace tailWord_2863250 prefixEnd_2863250 1470223483986027754907159 := by
  unfold tailWord_2863250
  simp only [CollatzResearch.WordTrace]
  refine ⟨26107826719235432253374801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69620871251294486008999469 26107826719235432253374801)
  ·
    refine ⟨19580870039426574190031101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26107826719235432253374801 19580870039426574190031101)
    ·
      refine ⟨7342826264784965321261663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19580870039426574190031101 7342826264784965321261663)
      ·
        refine ⟨11014239397177447981892495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7342826264784965321261663 11014239397177447981892495)
        ·
          refine ⟨16521359095766171972838743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11014239397177447981892495 16521359095766171972838743)
          ·
            refine ⟨24782038643649257959258115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16521359095766171972838743 24782038643649257959258115)
            ·
              refine ⟨37173057965473886938887173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24782038643649257959258115 37173057965473886938887173)
              ·
                refine ⟨6969948368526353801041345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37173057965473886938887173 6969948368526353801041345)
                ·
                  refine ⟨5227461276394765350781009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6969948368526353801041345 5227461276394765350781009)
                  ·
                    refine ⟨3920595957296074013085757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5227461276394765350781009 3920595957296074013085757)
                    ·
                      refine ⟨1470223483986027754907159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3920595957296074013085757 1470223483986027754907159)
                      ·
                        rfl

theorem cell23_2863250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_2863250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2863250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2863250 prefixEnd_2863250 := by exact prefixLift 2863250
  have htrace : WordTrace (prefixWord ++ tailWord_2863250) baseStart_2863250 baseEnd_2863250 := by
    simpa [prefixWord, tailWord_2863250, baseEnd_2863250] using wordTrace_append hprefix tailTrace_2863250
  have hstable : (prefixWord ++ tailWord_2863250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863250).length < 2 ^ (prefixWord ++ tailWord_2863250).sum := by decide
  have hdescent : baseEnd_2863250 < baseStart_2863250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863253 : List Nat := [1, 3, 2, 1, 1, 1, 6, 2, 6]
def baseStart_2863253 : Nat := 118140960795 + 2863253 * 2 ^ 59
def prefixEnd_2863253 : Nat := 4983230072969 + 3 ^ 40 * 2863253 * 2
def baseEnd_2863253 : Nat := 163358336047554582574405

theorem tailTrace_2863253 : CollatzResearch.WordTrace tailWord_2863253 prefixEnd_2863253 163358336047554582574405 := by
  unfold tailWord_2863253
  simp only [CollatzResearch.WordTrace]
  refine ⟨104431416295930860525858413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69620944197287240350572275 104431416295930860525858413)
  ·
    refine ⟨39161781110974072697196905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104431416295930860525858413 39161781110974072697196905)
    ·
      refine ⟨29371335833230554522897679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39161781110974072697196905 29371335833230554522897679)
      ·
        refine ⟨44057003749845831784346519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29371335833230554522897679 44057003749845831784346519)
        ·
          refine ⟨66085505624768747676519779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44057003749845831784346519 66085505624768747676519779)
          ·
            refine ⟨99128258437153121514779669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66085505624768747676519779 99128258437153121514779669)
            ·
              refine ⟨4646637114241552571005297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 99128258437153121514779669 4646637114241552571005297)
              ·
                refine ⟨3484977835681164428253973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4646637114241552571005297 3484977835681164428253973)
                ·
                  refine ⟨163358336047554582574405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3484977835681164428253973 163358336047554582574405)
                  ·
                    rfl

theorem cell23_2863253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 2, 6].length) (baseStart_2863253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2863253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2863253 prefixEnd_2863253 := by exact prefixLift 2863253
  have htrace : WordTrace (prefixWord ++ tailWord_2863253) baseStart_2863253 baseEnd_2863253 := by
    simpa [prefixWord, tailWord_2863253, baseEnd_2863253] using wordTrace_append hprefix tailTrace_2863253
  have hstable : (prefixWord ++ tailWord_2863253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863253).length < 2 ^ (prefixWord ++ tailWord_2863253).sum := by decide
  have hdescent : baseEnd_2863253 < baseStart_2863253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863276 : List Nat := [2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 5]
def baseStart_2863276 : Nat := 118140960795 + 2863276 * 2 ^ 59
def prefixEnd_2863276 : Nat := 4983230072969 + 3 ^ 40 * 2863276 * 2
def baseEnd_2863276 : Nat := 1470236834483044653182039

theorem tailTrace_2863276 : CollatzResearch.WordTrace tailWord_2863276 prefixEnd_2863276 1470236834483044653182039 := by
  unfold tailWord_2863276
  simp only [CollatzResearch.WordTrace]
  refine ⟨52216127587423767726972841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69621503449898356969297121 52216127587423767726972841)
  ·
    refine ⟨39162095690567825795229631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52216127587423767726972841 39162095690567825795229631)
    ·
      refine ⟨58743143535851738692844447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39162095690567825795229631 58743143535851738692844447)
      ·
        refine ⟨88114715303777608039266671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58743143535851738692844447 88114715303777608039266671)
        ·
          refine ⟨132172072955666412058900007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88114715303777608039266671 132172072955666412058900007)
          ·
            refine ⟨198258109433499618088350011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132172072955666412058900007 198258109433499618088350011)
            ·
              refine ⟨297387164150249427132525017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198258109433499618088350011 297387164150249427132525017)
              ·
                refine ⟨223040373112687070349393763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 297387164150249427132525017 223040373112687070349393763)
                ·
                  refine ⟨334560559669030605524090645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 223040373112687070349393763 334560559669030605524090645)
                  ·
                    refine ⟨15682526234485809633941749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 334560559669030605524090645 15682526234485809633941749)
                    ·
                      refine ⟨1470236834483044653182039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15682526234485809633941749 1470236834483044653182039)
                      ·
                        rfl

theorem cell23_2863276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 5].length) (baseStart_2863276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2863276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2863276 prefixEnd_2863276 := by exact prefixLift 2863276
  have htrace : WordTrace (prefixWord ++ tailWord_2863276) baseStart_2863276 baseEnd_2863276 := by
    simpa [prefixWord, tailWord_2863276, baseEnd_2863276] using wordTrace_append hprefix tailTrace_2863276
  have hstable : (prefixWord ++ tailWord_2863276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863276).length < 2 ^ (prefixWord ++ tailWord_2863276).sum := by decide
  have hdescent : baseEnd_2863276 < baseStart_2863276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
