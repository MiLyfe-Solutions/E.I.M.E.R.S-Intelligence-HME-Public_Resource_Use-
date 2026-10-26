import V185TrunkScan23Chunk0243

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1443833 : List Nat := [1, 2, 1, 3, 1, 4, 2, 2, 2, 3, 2]
def baseStart_1443833 : Nat := 118140960795 + 1443833 * 2 ^ 59
def prefixEnd_1443833 : Nat := 4983230072969 + 3 ^ 40 * 1443833 * 2
def baseEnd_1443833 : Nat := 741380313823154730447439

theorem tailTrace_1443833 : CollatzResearch.WordTrace tailWord_1443833 prefixEnd_1443833 741380313823154730447439 := by
  unfold tailWord_1443833
  simp only [CollatzResearch.WordTrace]
  refine ⟨52660915778247102889712153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35107277185498068593141435 52660915778247102889712153)
  ·
    refine ⟨39495686833685327167284115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52660915778247102889712153 39495686833685327167284115)
    ·
      refine ⟨59243530250527990750926173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39495686833685327167284115 59243530250527990750926173)
      ·
        refine ⟨22216323843947996531597315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59243530250527990750926173 22216323843947996531597315)
        ·
          refine ⟨33324485765921994797395973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22216323843947996531597315 33324485765921994797395973)
          ·
            refine ⟨6248341081110374024511745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33324485765921994797395973 6248341081110374024511745)
            ·
              refine ⟨4686255810832780518383809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6248341081110374024511745 4686255810832780518383809)
              ·
                refine ⟨3514691858124585388787857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4686255810832780518383809 3514691858124585388787857)
                ·
                  refine ⟨2636018893593439041590893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3514691858124585388787857 2636018893593439041590893)
                  ·
                    refine ⟨988507085097539640596585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2636018893593439041590893 988507085097539640596585)
                    ·
                      refine ⟨741380313823154730447439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 988507085097539640596585 741380313823154730447439)
                      ·
                        rfl

theorem cell23_1443833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 2, 2, 3, 2].length) (baseStart_1443833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1443833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1443833 prefixEnd_1443833 := by exact prefixLift 1443833
  have htrace : WordTrace (prefixWord ++ tailWord_1443833) baseStart_1443833 baseEnd_1443833 := by
    simpa [prefixWord, tailWord_1443833, baseEnd_1443833] using wordTrace_append hprefix tailTrace_1443833
  have hstable : (prefixWord ++ tailWord_1443833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443833).length < 2 ^ (prefixWord ++ tailWord_1443833).sum := by decide
  have hdescent : baseEnd_1443833 < baseStart_1443833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443859 : List Nat := [1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 6]
def baseStart_1443859 : Nat := 118140960795 + 1443859 * 2 ^ 59
def prefixEnd_1443859 : Nat := 4983230072969 + 3 ^ 40 * 1443859 * 2
def baseEnd_1443859 : Nat := 741393664320171628722319

theorem tailTrace_1443859 : CollatzResearch.WordTrace tailWord_1443859 prefixEnd_1443859 741393664320171628722319 := by
  unfold tailWord_1443859
  simp only [CollatzResearch.WordTrace]
  refine ⟨52661864076152909330158631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35107909384101939553439087 52661864076152909330158631)
  ·
    refine ⟨78992796114229363995237947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52661864076152909330158631 78992796114229363995237947)
    ·
      refine ⟨118489194171344045992856921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78992796114229363995237947 118489194171344045992856921)
      ·
        refine ⟨88866895628508034494642691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118489194171344045992856921 88866895628508034494642691)
        ·
          refine ⟨133300343442762051741964037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88866895628508034494642691 133300343442762051741964037)
          ·
            refine ⟨24993814395517884701618257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 133300343442762051741964037 24993814395517884701618257)
            ·
              refine ⟨18745360796638413526213693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24993814395517884701618257 18745360796638413526213693)
              ·
                refine ⟨7029510298739405072330135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18745360796638413526213693 7029510298739405072330135)
                ·
                  refine ⟨10544265448109107608495203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7029510298739405072330135 10544265448109107608495203)
                  ·
                    refine ⟨15816398172163661412742805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10544265448109107608495203 15816398172163661412742805)
                    ·
                      refine ⟨741393664320171628722319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15816398172163661412742805 741393664320171628722319)
                      ·
                        rfl

theorem cell23_1443859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 6].length) (baseStart_1443859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1443859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1443859 prefixEnd_1443859 := by exact prefixLift 1443859
  have htrace : WordTrace (prefixWord ++ tailWord_1443859) baseStart_1443859 baseEnd_1443859 := by
    simpa [prefixWord, tailWord_1443859, baseEnd_1443859] using wordTrace_append hprefix tailTrace_1443859
  have hstable : (prefixWord ++ tailWord_1443859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443859).length < 2 ^ (prefixWord ++ tailWord_1443859).sum := by decide
  have hdescent : baseEnd_1443859 < baseStart_1443859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443886 : List Nat := [4, 1, 3, 1, 1, 3, 10]
def baseStart_1443886 : Nat := 118140960795 + 1443886 * 2 ^ 59
def prefixEnd_1443886 : Nat := 4983230072969 + 3 ^ 40 * 1443886 * 2
def baseEnd_1443886 : Nat := 9153179361701765717095

theorem tailTrace_1443886 : CollatzResearch.WordTrace tailWord_1443886 prefixEnd_1443886 9153179361701765717095 := by
  unfold tailWord_1443886
  simp only [CollatzResearch.WordTrace]
  refine ⟨6582856105881886617673939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35108565898036728627594341 6582856105881886617673939)
  ·
    refine ⟨9874284158822829926510909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6582856105881886617673939 9874284158822829926510909)
    ·
      refine ⟨3702856559558561222441591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9874284158822829926510909 3702856559558561222441591)
      ·
        refine ⟨5554284839337841833662387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3702856559558561222441591 5554284839337841833662387)
        ·
          refine ⟨8331427259006762750493581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5554284839337841833662387 8331427259006762750493581)
          ·
            refine ⟨3124285222127536031435093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8331427259006762750493581 3124285222127536031435093)
            ·
              refine ⟨9153179361701765717095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3124285222127536031435093 9153179361701765717095)
              ·
                rfl

theorem cell23_1443886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 10].length) (baseStart_1443886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1443886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1443886 prefixEnd_1443886 := by exact prefixLift 1443886
  have htrace : WordTrace (prefixWord ++ tailWord_1443886) baseStart_1443886 baseEnd_1443886 := by
    simpa [prefixWord, tailWord_1443886, baseEnd_1443886] using wordTrace_append hprefix tailTrace_1443886
  have hstable : (prefixWord ++ tailWord_1443886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443886).length < 2 ^ (prefixWord ++ tailWord_1443886).sum := by decide
  have hdescent : baseEnd_1443886 < baseStart_1443886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443890 : List Nat := [3, 2, 1, 1, 2, 5, 1, 2, 2, 4]
def baseStart_1443890 : Nat := 118140960795 + 1443890 * 2 ^ 59
def prefixEnd_1443890 : Nat := 4983230072969 + 3 ^ 40 * 1443890 * 2
def baseEnd_1443890 : Nat := 247136527406820335811559

theorem tailTrace_1443890 : CollatzResearch.WordTrace tailWord_1443890 prefixEnd_1443890 247136527406820335811559 := by
  unfold tailWord_1443890
  simp only [CollatzResearch.WordTrace]
  refine ⟨13165748684760150406134281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35108663159360401083024749 13165748684760150406134281)
  ·
    refine ⟨9874311513570112804600711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13165748684760150406134281 9874311513570112804600711)
    ·
      refine ⟨14811467270355169206901067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9874311513570112804600711 14811467270355169206901067)
      ·
        refine ⟨22217200905532753810351601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14811467270355169206901067 22217200905532753810351601)
        ·
          refine ⟨16662900679149565357763701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22217200905532753810351601 16662900679149565357763701)
          ·
            refine ⟨1562146938670271752290347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16662900679149565357763701 1562146938670271752290347)
            ·
              refine ⟨2343220408005407628435521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1562146938670271752290347 2343220408005407628435521)
              ·
                refine ⟨1757415306004055721326641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2343220408005407628435521 1757415306004055721326641)
                ·
                  refine ⟨1318061479503041790994981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1757415306004055721326641 1318061479503041790994981)
                  ·
                    refine ⟨247136527406820335811559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1318061479503041790994981 247136527406820335811559)
                    ·
                      rfl

theorem cell23_1443890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 2, 2, 4].length) (baseStart_1443890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1443890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1443890 prefixEnd_1443890 := by exact prefixLift 1443890
  have htrace : WordTrace (prefixWord ++ tailWord_1443890) baseStart_1443890 baseEnd_1443890 := by
    simpa [prefixWord, tailWord_1443890, baseEnd_1443890] using wordTrace_append hprefix tailTrace_1443890
  have hstable : (prefixWord ++ tailWord_1443890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443890).length < 2 ^ (prefixWord ++ tailWord_1443890).sum := by decide
  have hdescent : baseEnd_1443890 < baseStart_1443890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443897 : List Nat := [1, 2, 1, 5, 3, 1, 2, 1, 3, 2, 2]
def baseStart_1443897 : Nat := 118140960795 + 1443897 * 2 ^ 59
def prefixEnd_1443897 : Nat := 4983230072969 + 3 ^ 40 * 1443897 * 2
def baseEnd_1443897 : Nat := 741413176585042480047145

theorem tailTrace_1443897 : CollatzResearch.WordTrace tailWord_1443897 prefixEnd_1443897 741413176585042480047145 := by
  unfold tailWord_1443897
  simp only [CollatzResearch.WordTrace]
  refine ⟨52663250050015241820041945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35108833366676827880027963 52663250050015241820041945)
  ·
    refine ⟨39497437537511431365031459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52663250050015241820041945 39497437537511431365031459)
    ·
      refine ⟨59246156306267147047547189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39497437537511431365031459 59246156306267147047547189)
      ·
        refine ⟨5554327153712545035707549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59246156306267147047547189 5554327153712545035707549)
        ·
          refine ⟨2082872682642204388390331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5554327153712545035707549 2082872682642204388390331)
          ·
            refine ⟨3124309023963306582585497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2082872682642204388390331 3124309023963306582585497)
            ·
              refine ⟨2343231767972479936939123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3124309023963306582585497 2343231767972479936939123)
              ·
                refine ⟨3514847651958719905408685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2343231767972479936939123 3514847651958719905408685)
                ·
                  refine ⟨1318067869484519964528257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3514847651958719905408685 1318067869484519964528257)
                  ·
                    refine ⟨988550902113389973396193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1318067869484519964528257 988550902113389973396193)
                    ·
                      refine ⟨741413176585042480047145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 988550902113389973396193 741413176585042480047145)
                      ·
                        rfl

theorem cell23_1443897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 1, 3, 2, 2].length) (baseStart_1443897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1443897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1443897 prefixEnd_1443897 := by exact prefixLift 1443897
  have htrace : WordTrace (prefixWord ++ tailWord_1443897) baseStart_1443897 baseEnd_1443897 := by
    simpa [prefixWord, tailWord_1443897, baseEnd_1443897] using wordTrace_append hprefix tailTrace_1443897
  have hstable : (prefixWord ++ tailWord_1443897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443897).length < 2 ^ (prefixWord ++ tailWord_1443897).sum := by decide
  have hdescent : baseEnd_1443897 < baseStart_1443897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443940 : List Nat := [2, 3, 1, 1, 2, 1, 4, 3, 1, 3, 2]
def baseStart_1443940 : Nat := 118140960795 + 1443940 * 2 ^ 59
def prefixEnd_1443940 : Nat := 4983230072969 + 3 ^ 40 * 1443940 * 2
def baseEnd_1443940 : Nat := 741435256253185811809447

theorem tailTrace_1443940 : CollatzResearch.WordTrace tailWord_1443940 prefixEnd_1443940 741435256253185811809447 := by
  unfold tailWord_1443940
  simp only [CollatzResearch.WordTrace]
  refine ⟨26332409194429730081928637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35109878925906306775904849 26332409194429730081928637)
  ·
    refine ⟨9874653447911148780723239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26332409194429730081928637 9874653447911148780723239)
    ·
      refine ⟨14811980171866723171084859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9874653447911148780723239 14811980171866723171084859)
      ·
        refine ⟨22217970257800084756627289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14811980171866723171084859 22217970257800084756627289)
        ·
          refine ⟨16663477693350063567470467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22217970257800084756627289 16663477693350063567470467)
          ·
            refine ⟨24995216540025095351205701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16663477693350063567470467 24995216540025095351205701)
            ·
              refine ⟨4686603101254705378351069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24995216540025095351205701 4686603101254705378351069)
              ·
                refine ⟨1757476162970514516881651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4686603101254705378351069 1757476162970514516881651)
                ·
                  refine ⟨2636214244455771775322477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1757476162970514516881651 2636214244455771775322477)
                  ·
                    refine ⟨988580341670914415745929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2636214244455771775322477 988580341670914415745929)
                    ·
                      refine ⟨741435256253185811809447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 988580341670914415745929 741435256253185811809447)
                      ·
                        rfl

theorem cell23_1443940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 3, 1, 3, 2].length) (baseStart_1443940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1443940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1443940 prefixEnd_1443940 := by exact prefixLift 1443940
  have htrace : WordTrace (prefixWord ++ tailWord_1443940) baseStart_1443940 baseEnd_1443940 := by
    simpa [prefixWord, tailWord_1443940, baseEnd_1443940] using wordTrace_append hprefix tailTrace_1443940
  have hstable : (prefixWord ++ tailWord_1443940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443940).length < 2 ^ (prefixWord ++ tailWord_1443940).sum := by decide
  have hdescent : baseEnd_1443940 < baseStart_1443940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444004 : List Nat := [2, 3, 1, 2, 4, 1, 2, 2, 2, 2, 2]
def baseStart_1444004 : Nat := 118140960795 + 1444004 * 2 ^ 59
def prefixEnd_1444004 : Nat := 4983230072969 + 3 ^ 40 * 1444004 * 2
def baseEnd_1444004 : Nat := 741468119015073561409153

theorem tailTrace_1444004 : CollatzResearch.WordTrace tailWord_1444004 prefixEnd_1444004 741468119015073561409153 := by
  unfold tailWord_1444004
  simp only [CollatzResearch.WordTrace]
  refine ⟨26333576330313799547093533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35111435107085066062791377 26333576330313799547093533)
  ·
    refine ⟨9875091123867674830160075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26333576330313799547093533 9875091123867674830160075)
    ·
      refine ⟨14812636685801512245240113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9875091123867674830160075 14812636685801512245240113)
      ·
        refine ⟨11109477514351134183930085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14812636685801512245240113 11109477514351134183930085)
        ·
          refine ⟨2083027033940837659486891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11109477514351134183930085 2083027033940837659486891)
          ·
            refine ⟨3124540550911256489230337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2083027033940837659486891 3124540550911256489230337)
            ·
              refine ⟨2343405413183442366922753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3124540550911256489230337 2343405413183442366922753)
              ·
                refine ⟨1757554059887581775192065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2343405413183442366922753 1757554059887581775192065)
                ·
                  refine ⟨1318165544915686331394049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1757554059887581775192065 1318165544915686331394049)
                  ·
                    refine ⟨988624158686764748545537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1318165544915686331394049 988624158686764748545537)
                    ·
                      refine ⟨741468119015073561409153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 988624158686764748545537 741468119015073561409153)
                      ·
                        rfl

theorem cell23_1444004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 2, 2, 2, 2].length) (baseStart_1444004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1444004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1444004 prefixEnd_1444004 := by exact prefixLift 1444004
  have htrace : WordTrace (prefixWord ++ tailWord_1444004) baseStart_1444004 baseEnd_1444004 := by
    simpa [prefixWord, tailWord_1444004, baseEnd_1444004] using wordTrace_append hprefix tailTrace_1444004
  have hstable : (prefixWord ++ tailWord_1444004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444004).length < 2 ^ (prefixWord ++ tailWord_1444004).sum := by decide
  have hdescent : baseEnd_1444004 < baseStart_1444004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444043 : List Nat := [1, 1, 1, 1, 3, 2, 3, 2, 1, 6, 2]
def baseStart_1444043 : Nat := 118140960795 + 1444043 * 2 ^ 59
def prefixEnd_1444043 : Nat := 4983230072969 + 3 ^ 40 * 1444043 * 2
def baseEnd_1444043 : Nat := 741488144760598908821473

theorem tailTrace_1444043 : CollatzResearch.WordTrace tailWord_1444043 prefixEnd_1444043 741488144760598908821473 := by
  unfold tailWord_1444043
  simp only [CollatzResearch.WordTrace]
  refine ⟨52668575107486308754856783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35112383404990872503237855 52668575107486308754856783)
  ·
    refine ⟨79002862661229463132285175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52668575107486308754856783 79002862661229463132285175)
    ·
      refine ⟨118504293991844194698427763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79002862661229463132285175 118504293991844194698427763)
      ·
        refine ⟨177756440987766292047641645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118504293991844194698427763 177756440987766292047641645)
        ·
          refine ⟨66658665370412359517865617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177756440987766292047641645 66658665370412359517865617)
          ·
            refine ⟨49993999027809269638399213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66658665370412359517865617 49993999027809269638399213)
            ·
              refine ⟨18747749635428476114399705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49993999027809269638399213 18747749635428476114399705)
              ·
                refine ⟨14060812226571357085799779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18747749635428476114399705 14060812226571357085799779)
                ·
                  refine ⟨21091218339857035628699669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14060812226571357085799779 21091218339857035628699669)
                  ·
                    refine ⟨988650859680798545095297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21091218339857035628699669 988650859680798545095297)
                    ·
                      refine ⟨741488144760598908821473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 988650859680798545095297 741488144760598908821473)
                      ·
                        rfl

theorem cell23_1444043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 6, 2].length) (baseStart_1444043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1444043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1444043 prefixEnd_1444043 := by exact prefixLift 1444043
  have htrace : WordTrace (prefixWord ++ tailWord_1444043) baseStart_1444043 baseEnd_1444043 := by
    simpa [prefixWord, tailWord_1444043, baseEnd_1444043] using wordTrace_append hprefix tailTrace_1444043
  have hstable : (prefixWord ++ tailWord_1444043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444043).length < 2 ^ (prefixWord ++ tailWord_1444043).sum := by decide
  have hdescent : baseEnd_1444043 < baseStart_1444043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444063 : List Nat := [1, 1, 2, 3, 2, 1, 1, 3, 4, 2, 3]
def baseStart_1444063 : Nat := 118140960795 + 1444063 * 2 ^ 59
def prefixEnd_1444063 : Nat := 4983230072969 + 3 ^ 40 * 1444063 * 2
def baseEnd_1444063 : Nat := 741498414373688830571381

theorem tailTrace_1444063 : CollatzResearch.WordTrace tailWord_1444063 prefixEnd_1444063 741498414373688830571381 := by
  unfold tailWord_1444063
  simp only [CollatzResearch.WordTrace]
  refine ⟨52669304567413852170584843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35112869711609234780389895 52669304567413852170584843)
  ·
    refine ⟨79003956851120778255877265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52669304567413852170584843 79003956851120778255877265)
    ·
      refine ⟨59252967638340583691907949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79003956851120778255877265 59252967638340583691907949)
      ·
        refine ⟨22219862864377718884465481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59252967638340583691907949 22219862864377718884465481)
        ·
          refine ⟨16664897148283289163349111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22219862864377718884465481 16664897148283289163349111)
          ·
            refine ⟨24997345722424933745023667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16664897148283289163349111 24997345722424933745023667)
            ·
              refine ⟨37496018583637400617535501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24997345722424933745023667 37496018583637400617535501)
              ·
                refine ⟨14061006968864025231575813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37496018583637400617535501 14061006968864025231575813)
                ·
                  refine ⟨2636438806662004730920465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14061006968864025231575813 2636438806662004730920465)
                  ·
                    refine ⟨1977329104996503548190349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2636438806662004730920465 1977329104996503548190349)
                    ·
                      refine ⟨741498414373688830571381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1977329104996503548190349 741498414373688830571381)
                      ·
                        rfl

theorem cell23_1444063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 4, 2, 3].length) (baseStart_1444063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1444063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1444063 prefixEnd_1444063 := by exact prefixLift 1444063
  have htrace : WordTrace (prefixWord ++ tailWord_1444063) baseStart_1444063 baseEnd_1444063 := by
    simpa [prefixWord, tailWord_1444063, baseEnd_1444063] using wordTrace_append hprefix tailTrace_1444063
  have hstable : (prefixWord ++ tailWord_1444063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444063).length < 2 ^ (prefixWord ++ tailWord_1444063).sum := by decide
  have hdescent : baseEnd_1444063 < baseStart_1444063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444104 : List Nat := [2, 1, 3, 2, 3, 3, 1, 3, 1, 4]
def baseStart_1444104 : Nat := 118140960795 + 1444104 * 2 ^ 59
def prefixEnd_1444104 : Nat := 4983230072969 + 3 ^ 40 * 1444104 * 2
def baseEnd_1444104 : Nat := 247173155693507723386231

theorem tailTrace_1444104 : CollatzResearch.WordTrace tailWord_1444104 prefixEnd_1444104 247173155693507723386231 := by
  unfold tailWord_1444104
  simp only [CollatzResearch.WordTrace]
  refine ⟨26335399980132658086413683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35113866640176877448551577 26335399980132658086413683)
  ·
    refine ⟨39503099970198987129620525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26335399980132658086413683 39503099970198987129620525)
    ·
      refine ⟨14813662488824620173607697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39503099970198987129620525 14813662488824620173607697)
      ·
        refine ⟨11110246866618465130205773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14813662488824620173607697 11110246866618465130205773)
        ·
          refine ⟨4166342574981924423827165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11110246866618465130205773 4166342574981924423827165)
          ·
            refine ⟨1562378465618221658935187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4166342574981924423827165 1562378465618221658935187)
            ·
              refine ⟨2343567698427332488402781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1562378465618221658935187 2343567698427332488402781)
              ·
                refine ⟨878837886910249683151043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2343567698427332488402781 878837886910249683151043)
                ·
                  refine ⟨1318256830365374524726565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 878837886910249683151043 1318256830365374524726565)
                  ·
                    refine ⟨247173155693507723386231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1318256830365374524726565 247173155693507723386231)
                    ·
                      rfl

theorem cell23_1444104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 3, 1, 4].length) (baseStart_1444104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1444104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1444104 prefixEnd_1444104 := by exact prefixLift 1444104
  have htrace : WordTrace (prefixWord ++ tailWord_1444104) baseStart_1444104 baseEnd_1444104 := by
    simpa [prefixWord, tailWord_1444104, baseEnd_1444104] using wordTrace_append hprefix tailTrace_1444104
  have hstable : (prefixWord ++ tailWord_1444104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444104).length < 2 ^ (prefixWord ++ tailWord_1444104).sum := by decide
  have hdescent : baseEnd_1444104 < baseStart_1444104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444127 : List Nat := [1, 1, 2, 4, 3, 1, 3, 1, 3, 1, 3]
def baseStart_1444127 : Nat := 118140960795 + 1444127 * 2 ^ 59
def prefixEnd_1444127 : Nat := 4983230072969 + 3 ^ 40 * 1444127 * 2
def baseEnd_1444127 : Nat := 741531277135576580171087

theorem tailTrace_1444127 : CollatzResearch.WordTrace tailWord_1444127 prefixEnd_1444127 741531277135576580171087 := by
  unfold tailWord_1444127
  simp only [CollatzResearch.WordTrace]
  refine ⟨52671638839181991100914635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35114425892787994067276423 52671638839181991100914635)
  ·
    refine ⟨79007458258772986651371953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52671638839181991100914635 79007458258772986651371953)
    ·
      refine ⟨59255593694079739988528965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79007458258772986651371953 59255593694079739988528965)
      ·
        refine ⟨11110423817639951247849181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59255593694079739988528965 11110423817639951247849181)
        ·
          refine ⟨4166408931614981717943443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11110423817639951247849181 4166408931614981717943443)
          ·
            refine ⟨6249613397422472576915165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4166408931614981717943443 6249613397422472576915165)
            ·
              refine ⟨2343605024033427216343187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6249613397422472576915165 2343605024033427216343187)
              ·
                refine ⟨3515407536050140824514781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2343605024033427216343187 3515407536050140824514781)
                ·
                  refine ⟨1318277826018802809193043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3515407536050140824514781 1318277826018802809193043)
                  ·
                    refine ⟨1977416739028204213789565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1318277826018802809193043 1977416739028204213789565)
                    ·
                      refine ⟨741531277135576580171087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1977416739028204213789565 741531277135576580171087)
                      ·
                        rfl

theorem cell23_1444127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 1, 3, 1, 3].length) (baseStart_1444127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1444127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1444127 prefixEnd_1444127 := by exact prefixLift 1444127
  have htrace : WordTrace (prefixWord ++ tailWord_1444127) baseStart_1444127 baseEnd_1444127 := by
    simpa [prefixWord, tailWord_1444127, baseEnd_1444127] using wordTrace_append hprefix tailTrace_1444127
  have hstable : (prefixWord ++ tailWord_1444127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444127).length < 2 ^ (prefixWord ++ tailWord_1444127).sum := by decide
  have hdescent : baseEnd_1444127 < baseStart_1444127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444163 : List Nat := [1, 1, 1, 3, 1, 3, 3, 1, 3, 2, 4]
def baseStart_1444163 : Nat := 118140960795 + 1444163 * 2 ^ 59
def prefixEnd_1444163 : Nat := 4983230072969 + 3 ^ 40 * 1444163 * 2
def baseEnd_1444163 : Nat := 741549762439138439320921

theorem tailTrace_1444163 : CollatzResearch.WordTrace tailWord_1444163 prefixEnd_1444163 741549762439138439320921 := by
  unfold tailWord_1444163
  simp only [CollatzResearch.WordTrace]
  refine ⟨52672951867051569249225143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35115301244701046166150095 52672951867051569249225143)
  ·
    refine ⟨79009427800577353873837715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52672951867051569249225143 79009427800577353873837715)
    ·
      refine ⟨118514141700866030810756573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79009427800577353873837715 118514141700866030810756573)
      ·
        refine ⟨44442803137824761554033715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118514141700866030810756573 44442803137824761554033715)
        ·
          refine ⟨66664204706737142331050573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44442803137824761554033715 66664204706737142331050573)
          ·
            refine ⟨24999076765026428374143965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66664204706737142331050573 24999076765026428374143965)
            ·
              refine ⟨9374653786884910640303987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24999076765026428374143965 9374653786884910640303987)
              ·
                refine ⟨14061980680327365960455981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9374653786884910640303987 14061980680327365960455981)
                ·
                  refine ⟨5273242755122762235170993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14061980680327365960455981 5273242755122762235170993)
                  ·
                    refine ⟨3954932066342071676378245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5273242755122762235170993 3954932066342071676378245)
                    ·
                      refine ⟨741549762439138439320921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3954932066342071676378245 741549762439138439320921)
                      ·
                        rfl

theorem cell23_1444163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 3, 2, 4].length) (baseStart_1444163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1444163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1444163 prefixEnd_1444163 := by exact prefixLift 1444163
  have htrace : WordTrace (prefixWord ++ tailWord_1444163) baseStart_1444163 baseEnd_1444163 := by
    simpa [prefixWord, tailWord_1444163, baseEnd_1444163] using wordTrace_append hprefix tailTrace_1444163
  have hstable : (prefixWord ++ tailWord_1444163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444163).length < 2 ^ (prefixWord ++ tailWord_1444163).sum := by decide
  have hdescent : baseEnd_1444163 < baseStart_1444163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444167 : List Nat := [1, 1, 4, 1, 2, 2, 5, 1, 1, 1, 4]
def baseStart_1444167 : Nat := 118140960795 + 1444167 * 2 ^ 59
def prefixEnd_1444167 : Nat := 4983230072969 + 3 ^ 40 * 1444167 * 2
def baseEnd_1444167 : Nat := 741551816361756423670903

theorem tailTrace_1444167 : CollatzResearch.WordTrace tailWord_1444167 prefixEnd_1444167 741551816361756423670903 := by
  unfold tailWord_1444167
  simp only [CollatzResearch.WordTrace]
  refine ⟨52673097759037077932370755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35115398506024718621580503 52673097759037077932370755)
  ·
    refine ⟨79009646638555616898556133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52673097759037077932370755 79009646638555616898556133)
    ·
      refine ⟨14814308744729178168479275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79009646638555616898556133 14814308744729178168479275)
      ·
        refine ⟨22221463117093767252718913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14814308744729178168479275 22221463117093767252718913)
        ·
          refine ⟨16666097337820325439539185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22221463117093767252718913 16666097337820325439539185)
          ·
            refine ⟨12499573003365244079654389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16666097337820325439539185 12499573003365244079654389)
            ·
              refine ⟨1171834969065491632467599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12499573003365244079654389 1171834969065491632467599)
              ·
                refine ⟨1757752453598237448701399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1171834969065491632467599 1757752453598237448701399)
                ·
                  refine ⟨2636628680397356173052099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1757752453598237448701399 2636628680397356173052099)
                  ·
                    refine ⟨3954943020596034259578149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2636628680397356173052099 3954943020596034259578149)
                    ·
                      refine ⟨741551816361756423670903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3954943020596034259578149 741551816361756423670903)
                      ·
                        rfl

theorem cell23_1444167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 5, 1, 1, 1, 4].length) (baseStart_1444167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1444167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1444167 prefixEnd_1444167 := by exact prefixLift 1444167
  have htrace : WordTrace (prefixWord ++ tailWord_1444167) baseStart_1444167 baseEnd_1444167 := by
    simpa [prefixWord, tailWord_1444167, baseEnd_1444167] using wordTrace_append hprefix tailTrace_1444167
  have hstable : (prefixWord ++ tailWord_1444167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444167).length < 2 ^ (prefixWord ++ tailWord_1444167).sum := by decide
  have hdescent : baseEnd_1444167 < baseStart_1444167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444173 : List Nat := [1, 6, 1, 15]
def baseStart_1444173 : Nat := 118140960795 + 1444173 * 2 ^ 59
def prefixEnd_1444173 : Nat := 4983230072969 + 3 ^ 40 * 1444173 * 2
def baseEnd_1444173 : Nat := 339074027089932967625

theorem tailTrace_1444173 : CollatzResearch.WordTrace tailWord_1444173 prefixEnd_1444173 339074027089932967625 := by
  unfold tailWord_1444173
  simp only [CollatzResearch.WordTrace]
  refine ⟨52673316597015340957089173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35115544398010227304726115 52673316597015340957089173)
  ·
    refine ⟨2469061715485094107363555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 52673316597015340957089173 2469061715485094107363555)
    ·
      refine ⟨3703592573227641161045333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2469061715485094107363555 3703592573227641161045333)
      ·
        refine ⟨339074027089932967625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 15 3703592573227641161045333 339074027089932967625)
        ·
          rfl

theorem cell23_1444173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 15].length) (baseStart_1444173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1444173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1444173 prefixEnd_1444173 := by exact prefixLift 1444173
  have htrace : WordTrace (prefixWord ++ tailWord_1444173) baseStart_1444173 baseEnd_1444173 := by
    simpa [prefixWord, tailWord_1444173, baseEnd_1444173] using wordTrace_append hprefix tailTrace_1444173
  have hstable : (prefixWord ++ tailWord_1444173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444173).length < 2 ^ (prefixWord ++ tailWord_1444173).sum := by decide
  have hdescent : baseEnd_1444173 < baseStart_1444173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444177 : List Nat := [1, 2, 2, 1, 4, 3, 2, 2, 2, 4]
def baseStart_1444177 : Nat := 118140960795 + 1444177 * 2 ^ 59
def prefixEnd_1444177 : Nat := 4983230072969 + 3 ^ 40 * 1444177 * 2
def baseEnd_1444177 : Nat := 247185650389433794848619

theorem tailTrace_1444177 : CollatzResearch.WordTrace tailWord_1444177 prefixEnd_1444177 247185650389433794848619 := by
  unfold tailWord_1444177
  simp only [CollatzResearch.WordTrace]
  refine ⟨52673462489000849640234785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35115641659333899760156523 52673462489000849640234785)
  ·
    refine ⟨39505096866750637230176089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52673462489000849640234785 39505096866750637230176089)
    ·
      refine ⟨29628822650062977922632067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39505096866750637230176089 29628822650062977922632067)
      ·
        refine ⟨44443233975094466883948101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29628822650062977922632067 44443233975094466883948101)
        ·
          refine ⟨8333106370330212540740269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44443233975094466883948101 8333106370330212540740269)
          ·
            refine ⟨3124914888873829702777601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8333106370330212540740269 3124914888873829702777601)
            ·
              refine ⟨2343686166655372277083201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3124914888873829702777601 2343686166655372277083201)
              ·
                refine ⟨1757764624991529207812401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2343686166655372277083201 1757764624991529207812401)
                ·
                  refine ⟨1318323468743646905859301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1757764624991529207812401 1318323468743646905859301)
                  ·
                    refine ⟨247185650389433794848619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1318323468743646905859301 247185650389433794848619)
                    ·
                      rfl

theorem cell23_1444177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 2, 2, 4].length) (baseStart_1444177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1444177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1444177 prefixEnd_1444177 := by exact prefixLift 1444177
  have htrace : WordTrace (prefixWord ++ tailWord_1444177) baseStart_1444177 baseEnd_1444177 := by
    simpa [prefixWord, tailWord_1444177, baseEnd_1444177] using wordTrace_append hprefix tailTrace_1444177
  have hstable : (prefixWord ++ tailWord_1444177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444177).length < 2 ^ (prefixWord ++ tailWord_1444177).sum := by decide
  have hdescent : baseEnd_1444177 < baseStart_1444177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444223 : List Nat := [1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 4]
def baseStart_1444223 : Nat := 118140960795 + 1444223 * 2 ^ 59
def prefixEnd_1444223 : Nat := 4983230072969 + 3 ^ 40 * 1444223 * 2
def baseEnd_1444223 : Nat := 741580571278408204570645

theorem tailTrace_1444223 : CollatzResearch.WordTrace tailWord_1444223 prefixEnd_1444223 741580571278408204570645 := by
  unfold tailWord_1444223
  simp only [CollatzResearch.WordTrace]
  refine ⟨52675140246834199496409323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35116760164556132997606215 52675140246834199496409323)
  ·
    refine ⟨79012710370251299244613985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52675140246834199496409323 79012710370251299244613985)
    ·
      refine ⟨59259532777688474433460489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79012710370251299244613985 59259532777688474433460489)
      ·
        refine ⟨44444649583266355825095367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59259532777688474433460489 44444649583266355825095367)
        ·
          refine ⟨66666974374899533737643051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44444649583266355825095367 66666974374899533737643051)
          ·
            refine ⟨100000461562349300606464577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66666974374899533737643051 100000461562349300606464577)
            ·
              refine ⟨75000346171761975454848433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100000461562349300606464577 75000346171761975454848433)
              ·
                refine ⟨56250259628821481591136325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75000346171761975454848433 56250259628821481591136325)
                ·
                  refine ⟨10546923680404027798338061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56250259628821481591136325 10546923680404027798338061)
                  ·
                    refine ⟨3955096380151510424376773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10546923680404027798338061 3955096380151510424376773)
                    ·
                      refine ⟨741580571278408204570645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3955096380151510424376773 741580571278408204570645)
                      ·
                        rfl

theorem cell23_1444223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 4].length) (baseStart_1444223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1444223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1444223 prefixEnd_1444223 := by exact prefixLift 1444223
  have htrace : WordTrace (prefixWord ++ tailWord_1444223) baseStart_1444223 baseEnd_1444223 := by
    simpa [prefixWord, tailWord_1444223, baseEnd_1444223] using wordTrace_append hprefix tailTrace_1444223
  have hstable : (prefixWord ++ tailWord_1444223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444223).length < 2 ^ (prefixWord ++ tailWord_1444223).sum := by decide
  have hdescent : baseEnd_1444223 < baseStart_1444223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444250 : List Nat := [3, 1, 1, 4, 1, 2, 2, 1, 2, 6]
def baseStart_1444250 : Nat := 118140960795 + 1444250 * 2 ^ 59
def prefixEnd_1444250 : Nat := 4983230072969 + 3 ^ 40 * 1444250 * 2
def baseEnd_1444250 : Nat := 247198145085359866311007

theorem tailTrace_1444250 : CollatzResearch.WordTrace tailWord_1444250 prefixEnd_1444250 247198145085359866311007 := by
  unfold tailWord_1444250
  simp only [CollatzResearch.WordTrace]
  refine ⟨13169031254434095776910551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35117416678490922071761469 13169031254434095776910551)
  ·
    refine ⟨19753546881651143665365827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13169031254434095776910551 19753546881651143665365827)
    ·
      refine ⟨29630320322476715498048741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19753546881651143665365827 29630320322476715498048741)
      ·
        refine ⟨5555685060464384155884139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29630320322476715498048741 5555685060464384155884139)
        ·
          refine ⟨8333527590696576233826209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5555685060464384155884139 8333527590696576233826209)
          ·
            refine ⟨6250145693022432175369657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8333527590696576233826209 6250145693022432175369657)
            ·
              refine ⟨4687609269766824131527243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6250145693022432175369657 4687609269766824131527243)
              ·
                refine ⟨7031413904650236197290865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4687609269766824131527243 7031413904650236197290865)
                ·
                  refine ⟨5273560428487677147968149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7031413904650236197290865 5273560428487677147968149)
                  ·
                    refine ⟨247198145085359866311007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5273560428487677147968149 247198145085359866311007)
                    ·
                      rfl

theorem cell23_1444250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 2, 6].length) (baseStart_1444250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1444250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1444250 prefixEnd_1444250 := by exact prefixLift 1444250
  have htrace : WordTrace (prefixWord ++ tailWord_1444250) baseStart_1444250 baseEnd_1444250 := by
    simpa [prefixWord, tailWord_1444250, baseEnd_1444250] using wordTrace_append hprefix tailTrace_1444250
  have hstable : (prefixWord ++ tailWord_1444250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444250).length < 2 ^ (prefixWord ++ tailWord_1444250).sum := by decide
  have hdescent : baseEnd_1444250 < baseStart_1444250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444260 : List Nat := [2, 3, 1, 2, 1, 1, 2, 2, 2, 4, 3]
def baseStart_1444260 : Nat := 118140960795 + 1444260 * 2 ^ 59
def prefixEnd_1444260 : Nat := 4983230072969 + 3 ^ 40 * 1444260 * 2
def baseEnd_1444260 : Nat := 741599570062624559807975

theorem tailTrace_1444260 : CollatzResearch.WordTrace tailWord_1444260 prefixEnd_1444260 741599570062624559807975 := by
  unfold tailWord_1444260
  simp only [CollatzResearch.WordTrace]
  refine ⟨26338244873850077407753117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35117659831800103210337489 26338244873850077407753117)
  ·
    refine ⟨9876841827693779027907419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26338244873850077407753117 9876841827693779027907419)
    ·
      refine ⟨14815262741540668541861129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9876841827693779027907419 14815262741540668541861129)
      ·
        refine ⟨11111447056155501406395847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14815262741540668541861129 11111447056155501406395847)
        ·
          refine ⟨16667170584233252109593771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11111447056155501406395847 16667170584233252109593771)
          ·
            refine ⟨25000755876349878164390657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16667170584233252109593771 25000755876349878164390657)
            ·
              refine ⟨18750566907262408623292993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25000755876349878164390657 18750566907262408623292993)
              ·
                refine ⟨14062925180446806467469745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18750566907262408623292993 14062925180446806467469745)
                ·
                  refine ⟨10547193885335104850602309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14062925180446806467469745 10547193885335104850602309)
                  ·
                    refine ⟨1977598853500332159487933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10547193885335104850602309 1977598853500332159487933)
                    ·
                      refine ⟨741599570062624559807975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1977598853500332159487933 741599570062624559807975)
                      ·
                        rfl

theorem cell23_1444260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 2, 4, 3].length) (baseStart_1444260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1444260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1444260 prefixEnd_1444260 := by exact prefixLift 1444260
  have htrace : WordTrace (prefixWord ++ tailWord_1444260) baseStart_1444260 baseEnd_1444260 := by
    simpa [prefixWord, tailWord_1444260, baseEnd_1444260] using wordTrace_append hprefix tailTrace_1444260
  have hstable : (prefixWord ++ tailWord_1444260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444260).length < 2 ^ (prefixWord ++ tailWord_1444260).sum := by decide
  have hdescent : baseEnd_1444260 < baseStart_1444260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444277 : List Nat := [1, 3, 3, 2, 3, 1, 1, 1, 2, 1, 5]
def baseStart_1444277 : Nat := 118140960795 + 1444277 * 2 ^ 59
def prefixEnd_1444277 : Nat := 4983230072969 + 3 ^ 40 * 1444277 * 2
def baseEnd_1444277 : Nat := 741608299233750993295397

theorem tailTrace_1444277 : CollatzResearch.WordTrace tailWord_1444277 prefixEnd_1444277 741608299233750993295397 := by
  unfold tailWord_1444277
  simp only [CollatzResearch.WordTrace]
  refine ⟨52677109788638566718875085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35118073192425711145916723 52677109788638566718875085)
  ·
    refine ⟨19753916170739462519578157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52677109788638566718875085 19753916170739462519578157)
    ·
      refine ⟨7407718564027298444841809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19753916170739462519578157 7407718564027298444841809)
      ·
        refine ⟨5555788923020473833631357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7407718564027298444841809 5555788923020473833631357)
        ·
          refine ⟨2083420846132677687611759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5555788923020473833631357 2083420846132677687611759)
          ·
            refine ⟨3125131269199016531417639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2083420846132677687611759 3125131269199016531417639)
            ·
              refine ⟨4687696903798524797126459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3125131269199016531417639 4687696903798524797126459)
              ·
                refine ⟨7031545355697787195689689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4687696903798524797126459 7031545355697787195689689)
                ·
                  refine ⟨5273659016773340396767267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7031545355697787195689689 5273659016773340396767267)
                  ·
                    refine ⟨7910488525160010595150901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5273659016773340396767267 7910488525160010595150901)
                    ·
                      refine ⟨741608299233750993295397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7910488525160010595150901 741608299233750993295397)
                      ·
                        rfl

theorem cell23_1444277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_1444277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1444277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1444277 prefixEnd_1444277 := by exact prefixLift 1444277
  have htrace : WordTrace (prefixWord ++ tailWord_1444277) baseStart_1444277 baseEnd_1444277 := by
    simpa [prefixWord, tailWord_1444277, baseEnd_1444277] using wordTrace_append hprefix tailTrace_1444277
  have hstable : (prefixWord ++ tailWord_1444277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444277).length < 2 ^ (prefixWord ++ tailWord_1444277).sum := by decide
  have hdescent : baseEnd_1444277 < baseStart_1444277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444293 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 2, 11]
def baseStart_1444293 : Nat := 118140960795 + 1444293 * 2 ^ 59
def prefixEnd_1444293 : Nat := 4983230072969 + 3 ^ 40 * 1444293 * 2
def baseEnd_1444293 : Nat := 247205504974740976898441

theorem tailTrace_1444293 : CollatzResearch.WordTrace tailWord_1444293 prefixEnd_1444293 247205504974740976898441 := by
  unfold tailWord_1444293
  simp only [CollatzResearch.WordTrace]
  refine ⟨52677693356580601451457533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35118462237720400967638355 52677693356580601451457533)
  ·
    refine ⟨19754135008717725544296575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52677693356580601451457533 19754135008717725544296575)
    ·
      refine ⟨29631202513076588316444863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19754135008717725544296575 29631202513076588316444863)
      ·
        refine ⟨44446803769614882474667295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29631202513076588316444863 44446803769614882474667295)
        ·
          refine ⟨66670205654422323712000943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44446803769614882474667295 66670205654422323712000943)
          ·
            refine ⟨100005308481633485568001415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66670205654422323712000943 100005308481633485568001415)
            ·
              refine ⟨150007962722450228352002123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100005308481633485568001415 150007962722450228352002123)
              ·
                refine ⟨225011944083675342528003185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150007962722450228352002123 225011944083675342528003185)
                ·
                  refine ⟨168758958062756506896002389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 225011944083675342528003185 168758958062756506896002389)
                  ·
                    refine ⟨247205504974740976898441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 168758958062756506896002389 247205504974740976898441)
                    ·
                      rfl

theorem cell23_1444293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 11].length) (baseStart_1444293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1444293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1444293 prefixEnd_1444293 := by exact prefixLift 1444293
  have htrace : WordTrace (prefixWord ++ tailWord_1444293) baseStart_1444293 baseEnd_1444293 := by
    simpa [prefixWord, tailWord_1444293, baseEnd_1444293] using wordTrace_append hprefix tailTrace_1444293
  have hstable : (prefixWord ++ tailWord_1444293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444293).length < 2 ^ (prefixWord ++ tailWord_1444293).sum := by decide
  have hdescent : baseEnd_1444293 < baseStart_1444293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444308 : List Nat := [2, 4, 1, 2, 2, 1, 4, 1, 2, 2, 2]
def baseStart_1444308 : Nat := 118140960795 + 1444308 * 2 ^ 59
def prefixEnd_1444308 : Nat := 4983230072969 + 3 ^ 40 * 1444308 * 2
def baseEnd_1444308 : Nat := 741624217134040372007755

theorem tailTrace_1444308 : CollatzResearch.WordTrace tailWord_1444308 prefixEnd_1444308 741624217134040372007755 := by
  unfold tailWord_1444308
  simp only [CollatzResearch.WordTrace]
  refine ⟨26339120225763129506626789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35118826967684172675502385 26339120225763129506626789)
  ·
    refine ⟨4938585042330586782492523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26339120225763129506626789 4938585042330586782492523)
    ·
      refine ⟨7407877563495880173738785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4938585042330586782492523 7407877563495880173738785)
      ·
        refine ⟨5555908172621910130304089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7407877563495880173738785 5555908172621910130304089)
        ·
          refine ⟨4166931129466432597728067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5555908172621910130304089 4166931129466432597728067)
          ·
            refine ⟨6250396694199648896592101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4166931129466432597728067 6250396694199648896592101)
            ·
              refine ⟨1171949380162434168111019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6250396694199648896592101 1171949380162434168111019)
              ·
                refine ⟨1757924070243651252166529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1171949380162434168111019 1757924070243651252166529)
                ·
                  refine ⟨1318443052682738439124897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1757924070243651252166529 1318443052682738439124897)
                  ·
                    refine ⟨988832289512053829343673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1318443052682738439124897 988832289512053829343673)
                    ·
                      refine ⟨741624217134040372007755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 988832289512053829343673 741624217134040372007755)
                      ·
                        rfl

theorem cell23_1444308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 4, 1, 2, 2, 2].length) (baseStart_1444308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1444308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1444308 prefixEnd_1444308 := by exact prefixLift 1444308
  have htrace : WordTrace (prefixWord ++ tailWord_1444308) baseStart_1444308 baseEnd_1444308 := by
    simpa [prefixWord, tailWord_1444308, baseEnd_1444308] using wordTrace_append hprefix tailTrace_1444308
  have hstable : (prefixWord ++ tailWord_1444308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444308).length < 2 ^ (prefixWord ++ tailWord_1444308).sum := by decide
  have hdescent : baseEnd_1444308 < baseStart_1444308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444327 : List Nat := [1, 1, 5, 2, 1, 1, 4, 1, 2, 5]
def baseStart_1444327 : Nat := 118140960795 + 1444327 * 2 ^ 59
def prefixEnd_1444327 : Nat := 4983230072969 + 3 ^ 40 * 1444327 * 2
def baseEnd_1444327 : Nat := 247211324422158599223389

theorem tailTrace_1444327 : CollatzResearch.WordTrace tailWord_1444327 prefixEnd_1444327 247211324422158599223389 := by
  unfold tailWord_1444327
  simp only [CollatzResearch.WordTrace]
  refine ⟨52678933438457425258195235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35119288958971616838796823 52678933438457425258195235)
  ·
    refine ⟨79018400157686137887292853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52678933438457425258195235 79018400157686137887292853)
    ·
      refine ⟨7407975014783075426933705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 79018400157686137887292853 7407975014783075426933705)
      ·
        refine ⟨5555981261087306570200279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7407975014783075426933705 5555981261087306570200279)
        ·
          refine ⟨8333971891630959855300419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5555981261087306570200279 8333971891630959855300419)
          ·
            refine ⟨12500957837446439782950629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8333971891630959855300419 12500957837446439782950629)
            ·
              refine ⟨2343929594521207459303243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12500957837446439782950629 2343929594521207459303243)
              ·
                refine ⟨3515894391781811188954865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2343929594521207459303243 3515894391781811188954865)
                ·
                  refine ⟨2636920793836358391716149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3515894391781811188954865 2636920793836358391716149)
                  ·
                    refine ⟨247211324422158599223389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2636920793836358391716149 247211324422158599223389)
                    ·
                      rfl

theorem cell23_1444327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 1, 2, 5].length) (baseStart_1444327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1444327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1444327 prefixEnd_1444327 := by exact prefixLift 1444327
  have htrace : WordTrace (prefixWord ++ tailWord_1444327) baseStart_1444327 baseEnd_1444327 := by
    simpa [prefixWord, tailWord_1444327, baseEnd_1444327] using wordTrace_append hprefix tailTrace_1444327
  have hstable : (prefixWord ++ tailWord_1444327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444327).length < 2 ^ (prefixWord ++ tailWord_1444327).sum := by decide
  have hdescent : baseEnd_1444327 < baseStart_1444327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444358 : List Nat := [6, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3]
def baseStart_1444358 : Nat := 118140960795 + 1444358 * 2 ^ 59
def prefixEnd_1444358 : Nat := 4983230072969 + 3 ^ 40 * 1444358 * 2
def baseEnd_1444358 : Nat := 741649891166765176382525

theorem tailTrace_1444358 : CollatzResearch.WordTrace tailWord_1444358 prefixEnd_1444358 741649891166765176382525 := by
  unfold tailWord_1444358
  simp only [CollatzResearch.WordTrace]
  refine ⟨1646252003167034923517929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 35120042734230078368382485 1646252003167034923517929)
  ·
    refine ⟨1234689002375276192638447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1646252003167034923517929 1234689002375276192638447)
    ·
      refine ⟨1852033503562914288957671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1234689002375276192638447 1852033503562914288957671)
      ·
        refine ⟨2778050255344371433436507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1852033503562914288957671 2778050255344371433436507)
        ·
          refine ⟨4167075383016557150154761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2778050255344371433436507 4167075383016557150154761)
          ·
            refine ⟨3125306537262417862616071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4167075383016557150154761 3125306537262417862616071)
            ·
              refine ⟨4687959805893626793924107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3125306537262417862616071 4687959805893626793924107)
              ·
                refine ⟨7031939708840440190886161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4687959805893626793924107 7031939708840440190886161)
                ·
                  refine ⟨5273954781630330143164621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7031939708840440190886161 5273954781630330143164621)
                  ·
                    refine ⟨1977733043111373803686733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5273954781630330143164621 1977733043111373803686733)
                    ·
                      refine ⟨741649891166765176382525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1977733043111373803686733 741649891166765176382525)
                      ·
                        rfl

theorem cell23_1444358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_1444358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1444358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1444358 prefixEnd_1444358 := by exact prefixLift 1444358
  have htrace : WordTrace (prefixWord ++ tailWord_1444358) baseStart_1444358 baseEnd_1444358 := by
    simpa [prefixWord, tailWord_1444358, baseEnd_1444358] using wordTrace_append hprefix tailTrace_1444358
  have hstable : (prefixWord ++ tailWord_1444358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444358).length < 2 ^ (prefixWord ++ tailWord_1444358).sum := by decide
  have hdescent : baseEnd_1444358 < baseStart_1444358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444360 : List Nat := [2, 1, 3, 2, 1, 1, 1, 2, 2, 4, 4]
def baseStart_1444360 : Nat := 118140960795 + 1444360 * 2 ^ 59
def prefixEnd_1444360 : Nat := 4983230072969 + 3 ^ 40 * 1444360 * 2
def baseEnd_1444360 : Nat := 741650918128074168557515

theorem tailTrace_1444360 : CollatzResearch.WordTrace tailWord_1444360 prefixEnd_1444360 741650918128074168557515 := by
  unfold tailWord_1444360
  simp only [CollatzResearch.WordTrace]
  refine ⟨26340068523668935947073267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35120091364891914596097689 26340068523668935947073267)
  ·
    refine ⟨39510102785503403920609901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26340068523668935947073267 39510102785503403920609901)
    ·
      refine ⟨14816288544563776470228713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39510102785503403920609901 14816288544563776470228713)
      ·
        refine ⟨11112216408422832352671535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14816288544563776470228713 11112216408422832352671535)
        ·
          refine ⟨16668324612634248529007303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11112216408422832352671535 16668324612634248529007303)
          ·
            refine ⟨25002486918951372793510955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16668324612634248529007303 25002486918951372793510955)
            ·
              refine ⟨37503730378427059190266433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25002486918951372793510955 37503730378427059190266433)
              ·
                refine ⟨28127797783820294392699825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37503730378427059190266433 28127797783820294392699825)
                ·
                  refine ⟨21095848337865220794524869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28127797783820294392699825 21095848337865220794524869)
                  ·
                    refine ⟨3955471563349728898973413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21095848337865220794524869 3955471563349728898973413)
                    ·
                      refine ⟨741650918128074168557515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3955471563349728898973413 741650918128074168557515)
                      ·
                        rfl

theorem cell23_1444360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_1444360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1444360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1444360 prefixEnd_1444360 := by exact prefixLift 1444360
  have htrace : WordTrace (prefixWord ++ tailWord_1444360) baseStart_1444360 baseEnd_1444360 := by
    simpa [prefixWord, tailWord_1444360, baseEnd_1444360] using wordTrace_append hprefix tailTrace_1444360
  have hstable : (prefixWord ++ tailWord_1444360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444360).length < 2 ^ (prefixWord ++ tailWord_1444360).sum := by decide
  have hdescent : baseEnd_1444360 < baseStart_1444360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444364 : List Nat := [2, 2, 1, 2, 4, 2, 1, 1, 2, 4, 2]
def baseStart_1444364 : Nat := 118140960795 + 1444364 * 2 ^ 59
def prefixEnd_1444364 : Nat := 4983230072969 + 3 ^ 40 * 1444364 * 2
def baseEnd_1444364 : Nat := 741652972050692152907497

theorem tailTrace_1444364 : CollatzResearch.WordTrace tailWord_1444364 prefixEnd_1444364 741652972050692152907497 := by
  unfold tailWord_1444364
  simp only [CollatzResearch.WordTrace]
  refine ⟨26340141469661690288646073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35120188626215587051528097 26340141469661690288646073)
  ·
    refine ⟨19755106102246267716484555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26340141469661690288646073 19755106102246267716484555)
    ·
      refine ⟨29632659153369401574726833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19755106102246267716484555 29632659153369401574726833)
      ·
        refine ⟨22224494365027051181045125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29632659153369401574726833 22224494365027051181045125)
        ·
          refine ⟨4167092693442572096445961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22224494365027051181045125 4167092693442572096445961)
          ·
            refine ⟨3125319520081929072334471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4167092693442572096445961 3125319520081929072334471)
            ·
              refine ⟨4687979280122893608501707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3125319520081929072334471 4687979280122893608501707)
              ·
                refine ⟨7031968920184340412752561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4687979280122893608501707 7031968920184340412752561)
                ·
                  refine ⟨5273976690138255309564421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7031968920184340412752561 5273976690138255309564421)
                  ·
                    refine ⟨988870629400922870543329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5273976690138255309564421 988870629400922870543329)
                    ·
                      refine ⟨741652972050692152907497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 988870629400922870543329 741652972050692152907497)
                      ·
                        rfl

theorem cell23_1444364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 2, 4, 2].length) (baseStart_1444364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1444364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1444364 prefixEnd_1444364 := by exact prefixLift 1444364
  have htrace : WordTrace (prefixWord ++ tailWord_1444364) baseStart_1444364 baseEnd_1444364 := by
    simpa [prefixWord, tailWord_1444364, baseEnd_1444364] using wordTrace_append hprefix tailTrace_1444364
  have hstable : (prefixWord ++ tailWord_1444364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444364).length < 2 ^ (prefixWord ++ tailWord_1444364).sum := by decide
  have hdescent : baseEnd_1444364 < baseStart_1444364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444384 : List Nat := [2, 1, 1, 6, 2, 1, 1, 1, 1, 4, 3]
def baseStart_1444384 : Nat := 118140960795 + 1444384 * 2 ^ 59
def prefixEnd_1444384 : Nat := 4983230072969 + 3 ^ 40 * 1444384 * 2
def baseEnd_1444384 : Nat := 741663241663782074657405

theorem tailTrace_1444384 : CollatzResearch.WordTrace tailWord_1444384 prefixEnd_1444384 741663241663782074657405 := by
  unfold tailWord_1444384
  simp only [CollatzResearch.WordTrace]
  refine ⟨26340506199625461996510103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35120674932833949328680137 26340506199625461996510103)
  ·
    refine ⟨39510759299438192994765155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26340506199625461996510103 39510759299438192994765155)
    ·
      refine ⟨59266138949157289492147733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39510759299438192994765155 59266138949157289492147733)
      ·
        refine ⟨2778100263241747944944425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 59266138949157289492147733 2778100263241747944944425)
        ·
          refine ⟨2083575197431310958708319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2778100263241747944944425 2083575197431310958708319)
          ·
            refine ⟨3125362796146966438062479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2083575197431310958708319 3125362796146966438062479)
            ·
              refine ⟨4688044194220449657093719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3125362796146966438062479 4688044194220449657093719)
              ·
                refine ⟨7032066291330674485640579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4688044194220449657093719 7032066291330674485640579)
                ·
                  refine ⟨10548099436996011728460869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7032066291330674485640579 10548099436996011728460869)
                  ·
                    refine ⟨1977768644436752199086413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10548099436996011728460869 1977768644436752199086413)
                    ·
                      refine ⟨741663241663782074657405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1977768644436752199086413 741663241663782074657405)
                      ·
                        rfl

theorem cell23_1444384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_1444384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1444384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1444384 prefixEnd_1444384 := by exact prefixLift 1444384
  have htrace : WordTrace (prefixWord ++ tailWord_1444384) baseStart_1444384 baseEnd_1444384 := by
    simpa [prefixWord, tailWord_1444384, baseEnd_1444384] using wordTrace_append hprefix tailTrace_1444384
  have hstable : (prefixWord ++ tailWord_1444384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444384).length < 2 ^ (prefixWord ++ tailWord_1444384).sum := by decide
  have hdescent : baseEnd_1444384 < baseStart_1444384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444434 : List Nat := [3, 2, 2, 1, 2, 1, 4, 2, 1, 5]
def baseStart_1444434 : Nat := 118140960795 + 1444434 * 2 ^ 59
def prefixEnd_1444434 : Nat := 4983230072969 + 3 ^ 40 * 1444434 * 2
def baseEnd_1444434 : Nat := 247229638565502293010725

theorem tailTrace_1444434 : CollatzResearch.WordTrace tailWord_1444434 prefixEnd_1444434 247229638565502293010725 := by
  unfold tailWord_1444434
  simp only [CollatzResearch.WordTrace]
  refine ⟨13170709012267445633085089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35121890699379855021560237 13170709012267445633085089)
  ·
    refine ⟨9878031759200584224813817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13170709012267445633085089 9878031759200584224813817)
    ·
      refine ⟨7408523819400438168610363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9878031759200584224813817 7408523819400438168610363)
      ·
        refine ⟨11112785729100657252915545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7408523819400438168610363 11112785729100657252915545)
        ·
          refine ⟨8334589296825492939686659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11112785729100657252915545 8334589296825492939686659)
          ·
            refine ⟨12501883945238239409529989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8334589296825492939686659 12501883945238239409529989)
            ·
              refine ⟨2344103239732169889286873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12501883945238239409529989 2344103239732169889286873)
              ·
                refine ⟨1758077429799127416965155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2344103239732169889286873 1758077429799127416965155)
                ·
                  refine ⟨2637116144698691125447733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1758077429799127416965155 2637116144698691125447733)
                  ·
                    refine ⟨247229638565502293010725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2637116144698691125447733 247229638565502293010725)
                    ·
                      rfl

theorem cell23_1444434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 2, 1, 5].length) (baseStart_1444434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1444434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1444434 prefixEnd_1444434 := by exact prefixLift 1444434
  have htrace : WordTrace (prefixWord ++ tailWord_1444434) baseStart_1444434 baseEnd_1444434 := by
    simpa [prefixWord, tailWord_1444434, baseEnd_1444434] using wordTrace_append hprefix tailTrace_1444434
  have hstable : (prefixWord ++ tailWord_1444434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444434).length < 2 ^ (prefixWord ++ tailWord_1444434).sum := by decide
  have hdescent : baseEnd_1444434 < baseStart_1444434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444437 : List Nat := [1, 3, 2, 2, 1, 1, 2, 3, 3, 1, 4]
def baseStart_1444437 : Nat := 118140960795 + 1444437 * 2 ^ 59
def prefixEnd_1444437 : Nat := 4983230072969 + 3 ^ 40 * 1444437 * 2
def baseEnd_1444437 : Nat := 741690456138470367294661

theorem tailTrace_1444437 : CollatzResearch.WordTrace tailWord_1444437 prefixEnd_1444437 741690456138470367294661 := by
  unfold tailWord_1444437
  simp only [CollatzResearch.WordTrace]
  refine ⟨52682945468058914044699565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35121963645372609363133043 52682945468058914044699565)
  ·
    refine ⟨19756104550522092766762337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52682945468058914044699565 19756104550522092766762337)
    ·
      refine ⟨14817078412891569575071753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19756104550522092766762337 14817078412891569575071753)
      ·
        refine ⟨11112808809668677181303815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14817078412891569575071753 11112808809668677181303815)
        ·
          refine ⟨16669213214503015771955723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11112808809668677181303815 16669213214503015771955723)
          ·
            refine ⟨25003819821754523657933585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16669213214503015771955723 25003819821754523657933585)
            ·
              refine ⟨18752864866315892743450189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25003819821754523657933585 18752864866315892743450189)
              ·
                refine ⟨7032324324868459778793821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18752864866315892743450189 7032324324868459778793821)
                ·
                  refine ⟨2637121621825672417047683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7032324324868459778793821 2637121621825672417047683)
                  ·
                    refine ⟨3955682432738508625571525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2637121621825672417047683 3955682432738508625571525)
                    ·
                      refine ⟨741690456138470367294661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3955682432738508625571525 741690456138470367294661)
                      ·
                        rfl

theorem cell23_1444437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_1444437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1444437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1444437 prefixEnd_1444437 := by exact prefixLift 1444437
  have htrace : WordTrace (prefixWord ++ tailWord_1444437) baseStart_1444437 baseEnd_1444437 := by
    simpa [prefixWord, tailWord_1444437, baseEnd_1444437] using wordTrace_append hprefix tailTrace_1444437
  have hstable : (prefixWord ++ tailWord_1444437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444437).length < 2 ^ (prefixWord ++ tailWord_1444437).sum := by decide
  have hdescent : baseEnd_1444437 < baseStart_1444437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444457 : List Nat := [1, 2, 1, 1, 1, 4, 1, 2, 5, 2, 3]
def baseStart_1444457 : Nat := 118140960795 + 1444457 * 2 ^ 59
def prefixEnd_1444457 : Nat := 4983230072969 + 3 ^ 40 * 1444457 * 2
def baseEnd_1444457 : Nat := 741700725751560289044569

theorem tailTrace_1444457 : CollatzResearch.WordTrace tailWord_1444457 prefixEnd_1444457 741700725751560289044569 := by
  unfold tailWord_1444457
  simp only [CollatzResearch.WordTrace]
  refine ⟨52683674927986457460427625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35122449951990971640285083 52683674927986457460427625)
  ·
    refine ⟨39512756195989843095320719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52683674927986457460427625 39512756195989843095320719)
    ·
      refine ⟨59269134293984764642981079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39512756195989843095320719 59269134293984764642981079)
      ·
        refine ⟨88903701440977146964471619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59269134293984764642981079 88903701440977146964471619)
        ·
          refine ⟨133355552161465720446707429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88903701440977146964471619 133355552161465720446707429)
          ·
            refine ⟨25004166030274822583757643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 133355552161465720446707429 25004166030274822583757643)
            ·
              refine ⟨37506249045412233875636465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25004166030274822583757643 37506249045412233875636465)
              ·
                refine ⟨28129686784059175406727349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37506249045412233875636465 28129686784059175406727349)
                ·
                  refine ⟨2637158136005547694380689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28129686784059175406727349 2637158136005547694380689)
                  ·
                    refine ⟨1977868602004160770785517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2637158136005547694380689 1977868602004160770785517)
                    ·
                      refine ⟨741700725751560289044569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1977868602004160770785517 741700725751560289044569)
                      ·
                        rfl

theorem cell23_1444457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 5, 2, 3].length) (baseStart_1444457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1444457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1444457 prefixEnd_1444457 := by exact prefixLift 1444457
  have htrace : WordTrace (prefixWord ++ tailWord_1444457) baseStart_1444457 baseEnd_1444457 := by
    simpa [prefixWord, tailWord_1444457, baseEnd_1444457] using wordTrace_append hprefix tailTrace_1444457
  have hstable : (prefixWord ++ tailWord_1444457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444457).length < 2 ^ (prefixWord ++ tailWord_1444457).sum := by decide
  have hdescent : baseEnd_1444457 < baseStart_1444457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444460 : List Nat := [2, 2, 1, 1, 3, 1, 13]
def baseStart_1444460 : Nat := 118140960795 + 1444460 * 2 ^ 59
def prefixEnd_1444460 : Nat := 4983230072969 + 3 ^ 40 * 1444460 * 2
def baseEnd_1444460 : Nat := 9156818101154614534655

theorem tailTrace_1444460 : CollatzResearch.WordTrace tailWord_1444460 prefixEnd_1444460 9156818101154614534655 := by
  unfold tailWord_1444460
  simp only [CollatzResearch.WordTrace]
  refine ⟨26341892173487794486393417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35122522897983725981857889 26341892173487794486393417)
  ·
    refine ⟨19756419130115845864795063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26341892173487794486393417 19756419130115845864795063)
    ·
      refine ⟨29634628695173768797192595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19756419130115845864795063 29634628695173768797192595)
      ·
        refine ⟨44451943042760653195788893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29634628695173768797192595 44451943042760653195788893)
        ·
          refine ⟨16669478641035244948420835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44451943042760653195788893 16669478641035244948420835)
          ·
            refine ⟨25004217961552867422631253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16669478641035244948420835 25004217961552867422631253)
            ·
              refine ⟨9156818101154614534655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 25004217961552867422631253 9156818101154614534655)
              ·
                rfl

theorem cell23_1444460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 13].length) (baseStart_1444460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1444460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1444460 prefixEnd_1444460 := by exact prefixLift 1444460
  have htrace : WordTrace (prefixWord ++ tailWord_1444460) baseStart_1444460 baseEnd_1444460 := by
    simpa [prefixWord, tailWord_1444460, baseEnd_1444460] using wordTrace_append hprefix tailTrace_1444460
  have hstable : (prefixWord ++ tailWord_1444460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444460).length < 2 ^ (prefixWord ++ tailWord_1444460).sum := by decide
  have hdescent : baseEnd_1444460 < baseStart_1444460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444471 : List Nat := [1, 1, 3, 1, 1, 3, 5, 1, 3, 2, 2]
def baseStart_1444471 : Nat := 118140960795 + 1444471 * 2 ^ 59
def prefixEnd_1444471 : Nat := 4983230072969 + 3 ^ 40 * 1444471 * 2
def baseEnd_1444471 : Nat := 741707914480723234269505

theorem tailTrace_1444471 : CollatzResearch.WordTrace tailWord_1444471 prefixEnd_1444471 741707914480723234269505 := by
  unfold tailWord_1444471
  simp only [CollatzResearch.WordTrace]
  refine ⟨52684185549935737851437267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35122790366623825234291511 52684185549935737851437267)
  ·
    refine ⟨79026278324903606777155901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52684185549935737851437267 79026278324903606777155901)
    ·
      refine ⟨29634854371838852541433463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79026278324903606777155901 29634854371838852541433463)
      ·
        refine ⟨44452281557758278812150195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29634854371838852541433463 44452281557758278812150195)
        ·
          refine ⟨66678422336637418218225293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44452281557758278812150195 66678422336637418218225293)
          ·
            refine ⟨25004408376239031831834485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66678422336637418218225293 25004408376239031831834485)
            ·
              refine ⟨2344163285272409234234483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25004408376239031831834485 2344163285272409234234483)
              ·
                refine ⟨3516244927908613851351725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2344163285272409234234483 3516244927908613851351725)
                ·
                  refine ⟨1318591847965730194256897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3516244927908613851351725 1318591847965730194256897)
                  ·
                    refine ⟨988943885974297645692673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1318591847965730194256897 988943885974297645692673)
                    ·
                      refine ⟨741707914480723234269505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 988943885974297645692673 741707914480723234269505)
                      ·
                        rfl

theorem cell23_1444471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 1, 3, 2, 2].length) (baseStart_1444471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1444471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1444471 prefixEnd_1444471 := by exact prefixLift 1444471
  have htrace : WordTrace (prefixWord ++ tailWord_1444471) baseStart_1444471 baseEnd_1444471 := by
    simpa [prefixWord, tailWord_1444471, baseEnd_1444471] using wordTrace_append hprefix tailTrace_1444471
  have hstable : (prefixWord ++ tailWord_1444471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444471).length < 2 ^ (prefixWord ++ tailWord_1444471).sum := by decide
  have hdescent : baseEnd_1444471 < baseStart_1444471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444504 : List Nat := [2, 1, 2, 4, 1, 1, 3, 2, 1, 3, 3]
def baseStart_1444504 : Nat := 118140960795 + 1444504 * 2 ^ 59
def prefixEnd_1444504 : Nat := 4983230072969 + 3 ^ 40 * 1444504 * 2
def baseEnd_1444504 : Nat := 741724859342321605156853

theorem tailTrace_1444504 : CollatzResearch.WordTrace tailWord_1444504 prefixEnd_1444504 741724859342321605156853 := by
  unfold tailWord_1444504
  simp only [CollatzResearch.WordTrace]
  refine ⟨26342694579408092243694283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35123592772544122991592377 26342694579408092243694283)
  ·
    refine ⟨39514041869112138365541425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26342694579408092243694283 39514041869112138365541425)
    ·
      refine ⟨29635531401834103774156069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39514041869112138365541425 29635531401834103774156069)
      ·
        refine ⟨5556662137843894457654263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29635531401834103774156069 5556662137843894457654263)
        ·
          refine ⟨8334993206765841686481395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5556662137843894457654263 8334993206765841686481395)
          ·
            refine ⟨12502489810148762529722093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8334993206765841686481395 12502489810148762529722093)
            ·
              refine ⟨4688433678805785948645785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12502489810148762529722093 4688433678805785948645785)
              ·
                refine ⟨3516325259104339461484339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4688433678805785948645785 3516325259104339461484339)
                ·
                  refine ⟨5274487888656509192226509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3516325259104339461484339 5274487888656509192226509)
                  ·
                    refine ⟨1977932958246190947084941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5274487888656509192226509 1977932958246190947084941)
                    ·
                      refine ⟨741724859342321605156853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1977932958246190947084941 741724859342321605156853)
                      ·
                        rfl

theorem cell23_1444504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_1444504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1444504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1444504 prefixEnd_1444504 := by exact prefixLift 1444504
  have htrace : WordTrace (prefixWord ++ tailWord_1444504) baseStart_1444504 baseEnd_1444504 := by
    simpa [prefixWord, tailWord_1444504, baseEnd_1444504] using wordTrace_append hprefix tailTrace_1444504
  have hstable : (prefixWord ++ tailWord_1444504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444504).length < 2 ^ (prefixWord ++ tailWord_1444504).sum := by decide
  have hdescent : baseEnd_1444504 < baseStart_1444504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444508 : List Nat := [2, 2, 3, 2, 2, 2, 3, 1, 1, 2, 3]
def baseStart_1444508 : Nat := 118140960795 + 1444508 * 2 ^ 59
def prefixEnd_1444508 : Nat := 4983230072969 + 3 ^ 40 * 1444508 * 2
def baseEnd_1444508 : Nat := 741726913264939589506835

theorem tailTrace_1444508 : CollatzResearch.WordTrace tailWord_1444508 prefixEnd_1444508 741726913264939589506835 := by
  unfold tailWord_1444508
  simp only [CollatzResearch.WordTrace]
  refine ⟨26342767525400846585267089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35123690033867795447022785 26342767525400846585267089)
  ·
    refine ⟨19757075644050634938950317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26342767525400846585267089 19757075644050634938950317)
    ·
      refine ⟨7408903366518988102106369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19757075644050634938950317 7408903366518988102106369)
      ·
        refine ⟨5556677524889241076579777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7408903366518988102106369 5556677524889241076579777)
        ·
          refine ⟨4167508143666930807434833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5556677524889241076579777 4167508143666930807434833)
          ·
            refine ⟨3125631107750198105576125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4167508143666930807434833 3125631107750198105576125)
            ·
              refine ⟨1172111665406324289591047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3125631107750198105576125 1172111665406324289591047)
              ·
                refine ⟨1758167498109486434386571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1172111665406324289591047 1758167498109486434386571)
                ·
                  refine ⟨2637251247164229651579857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1758167498109486434386571 2637251247164229651579857)
                  ·
                    refine ⟨1977938435373172238684893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2637251247164229651579857 1977938435373172238684893)
                    ·
                      refine ⟨741726913264939589506835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1977938435373172238684893 741726913264939589506835)
                      ·
                        rfl

theorem cell23_1444508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 3, 1, 1, 2, 3].length) (baseStart_1444508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1444508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1444508 prefixEnd_1444508 := by exact prefixLift 1444508
  have htrace : WordTrace (prefixWord ++ tailWord_1444508) baseStart_1444508 baseEnd_1444508 := by
    simpa [prefixWord, tailWord_1444508, baseEnd_1444508] using wordTrace_append hprefix tailTrace_1444508
  have hstable : (prefixWord ++ tailWord_1444508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444508).length < 2 ^ (prefixWord ++ tailWord_1444508).sum := by decide
  have hdescent : baseEnd_1444508 < baseStart_1444508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444527 : List Nat := [1, 1, 2, 1, 2, 5, 1, 1, 2, 3, 4]
def baseStart_1444527 : Nat := 118140960795 + 1444527 * 2 ^ 59
def prefixEnd_1444527 : Nat := 4983230072969 + 3 ^ 40 * 1444527 * 2
def baseEnd_1444527 : Nat := 741736669397375015169247

theorem tailTrace_1444527 : CollatzResearch.WordTrace tailWord_1444527 prefixEnd_1444527 741736669397375015169247 := by
  unfold tailWord_1444527
  simp only [CollatzResearch.WordTrace]
  refine ⟨52686228037732859415475835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35124152025155239610317223 52686228037732859415475835)
  ·
    refine ⟨79029342056599289123213753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52686228037732859415475835 79029342056599289123213753)
    ·
      refine ⟨59272006542449466842410315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79029342056599289123213753 59272006542449466842410315)
      ·
        refine ⟨88908009813674200263615473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59272006542449466842410315 88908009813674200263615473)
        ·
          refine ⟨66681007360255650197711605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88908009813674200263615473 66681007360255650197711605)
          ·
            refine ⟨6251344440023967206035463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 66681007360255650197711605 6251344440023967206035463)
            ·
              refine ⟨9377016660035950809053195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6251344440023967206035463 9377016660035950809053195)
              ·
                refine ⟨14065524990053926213579793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9377016660035950809053195 14065524990053926213579793)
                ·
                  refine ⟨10549143742540444660184845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14065524990053926213579793 10549143742540444660184845)
                  ·
                    refine ⟨3955928903452666747569317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10549143742540444660184845 3955928903452666747569317)
                    ·
                      refine ⟨741736669397375015169247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3955928903452666747569317 741736669397375015169247)
                      ·
                        rfl

theorem cell23_1444527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 3, 4].length) (baseStart_1444527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1444527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1444527 prefixEnd_1444527 := by exact prefixLift 1444527
  have htrace : WordTrace (prefixWord ++ tailWord_1444527) baseStart_1444527 baseEnd_1444527 := by
    simpa [prefixWord, tailWord_1444527, baseEnd_1444527] using wordTrace_append hprefix tailTrace_1444527
  have hstable : (prefixWord ++ tailWord_1444527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444527).length < 2 ^ (prefixWord ++ tailWord_1444527).sum := by decide
  have hdescent : baseEnd_1444527 < baseStart_1444527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444561 : List Nat := [1, 2, 2, 1, 2, 3, 2, 2, 4, 2, 2]
def baseStart_1444561 : Nat := 118140960795 + 1444561 * 2 ^ 59
def prefixEnd_1444561 : Nat := 4983230072969 + 3 ^ 40 * 1444561 * 2
def baseEnd_1444561 : Nat := 741754127739627882144091

theorem tailTrace_1444561 : CollatzResearch.WordTrace tailWord_1444561 prefixEnd_1444561 741754127739627882144091 := by
  unfold tailWord_1444561
  simp only [CollatzResearch.WordTrace]
  refine ⟨52687468119609683222213537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35124978746406455481475691 52687468119609683222213537)
  ·
    refine ⟨39515601089707262416660153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52687468119609683222213537 39515601089707262416660153)
    ·
      refine ⟨29636700817280446812495115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39515601089707262416660153 29636700817280446812495115)
      ·
        refine ⟨44455051225920670218742673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29636700817280446812495115 44455051225920670218742673)
        ·
          refine ⟨33341288419440502664057005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44455051225920670218742673 33341288419440502664057005)
          ·
            refine ⟨12502983157290188499021377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33341288419440502664057005 12502983157290188499021377)
            ·
              refine ⟨9377237367967641374266033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12502983157290188499021377 9377237367967641374266033)
              ·
                refine ⟨7032928025975731030699525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9377237367967641374266033 7032928025975731030699525)
                ·
                  refine ⟨1318674004870449568256161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7032928025975731030699525 1318674004870449568256161)
                  ·
                    refine ⟨989005503652837176192121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1318674004870449568256161 989005503652837176192121)
                    ·
                      refine ⟨741754127739627882144091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 989005503652837176192121 741754127739627882144091)
                      ·
                        rfl

theorem cell23_1444561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 4, 2, 2].length) (baseStart_1444561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1444561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1444561 prefixEnd_1444561 := by exact prefixLift 1444561
  have htrace : WordTrace (prefixWord ++ tailWord_1444561) baseStart_1444561 baseEnd_1444561 := by
    simpa [prefixWord, tailWord_1444561, baseEnd_1444561] using wordTrace_append hprefix tailTrace_1444561
  have hstable : (prefixWord ++ tailWord_1444561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444561).length < 2 ^ (prefixWord ++ tailWord_1444561).sum := by decide
  have hdescent : baseEnd_1444561 < baseStart_1444561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444565 : List Nat := [1, 3, 2, 5, 1, 1, 1, 3, 1, 3, 2]
def baseStart_1444565 : Nat := 118140960795 + 1444565 * 2 ^ 59
def prefixEnd_1444565 : Nat := 4983230072969 + 3 ^ 40 * 1444565 * 2
def baseEnd_1444565 : Nat := 741756181662245866494073

theorem tailTrace_1444565 : CollatzResearch.WordTrace tailWord_1444565 prefixEnd_1444565 741756181662245866494073 := by
  unfold tailWord_1444565
  simp only [CollatzResearch.WordTrace]
  refine ⟨52687614011595191905359149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35125076007730127936906099 52687614011595191905359149)
  ·
    refine ⟨19757855254348196964509681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52687614011595191905359149 19757855254348196964509681)
    ·
      refine ⟨14818391440761147723382261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19757855254348196964509681 14818391440761147723382261)
      ·
        refine ⟨1389224197571357599067087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14818391440761147723382261 1389224197571357599067087)
        ·
          refine ⟨2083836296357036398600631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1389224197571357599067087 2083836296357036398600631)
          ·
            refine ⟨3125754444535554597900947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2083836296357036398600631 3125754444535554597900947)
            ·
              refine ⟨4688631666803331896851421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3125754444535554597900947 4688631666803331896851421)
              ·
                refine ⟨1758236875051249461319283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4688631666803331896851421 1758236875051249461319283)
                ·
                  refine ⟨2637355312576874191978925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1758236875051249461319283 2637355312576874191978925)
                  ·
                    refine ⟨989008242216327821992097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2637355312576874191978925 989008242216327821992097)
                    ·
                      refine ⟨741756181662245866494073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 989008242216327821992097 741756181662245866494073)
                      ·
                        rfl

theorem cell23_1444565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_1444565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1444565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1444565 prefixEnd_1444565 := by exact prefixLift 1444565
  have htrace : WordTrace (prefixWord ++ tailWord_1444565) baseStart_1444565 baseEnd_1444565 := by
    simpa [prefixWord, tailWord_1444565, baseEnd_1444565] using wordTrace_append hprefix tailTrace_1444565
  have hstable : (prefixWord ++ tailWord_1444565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444565).length < 2 ^ (prefixWord ++ tailWord_1444565).sum := by decide
  have hdescent : baseEnd_1444565 < baseStart_1444565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444607 : List Nat := [1, 1, 2, 2, 1, 3, 1, 2, 3, 2, 5]
def baseStart_1444607 : Nat := 118140960795 + 1444607 * 2 ^ 59
def prefixEnd_1444607 : Nat := 4983230072969 + 3 ^ 40 * 1444607 * 2
def baseEnd_1444607 : Nat := 741777747849734702168879

theorem tailTrace_1444607 : CollatzResearch.WordTrace tailWord_1444607 prefixEnd_1444607 741777747849734702168879 := by
  unfold tailWord_1444607
  simp only [CollatzResearch.WordTrace]
  refine ⟨52689145877443033078388075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35126097251628688718925383 52689145877443033078388075)
  ·
    refine ⟨79033718816164549617582113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52689145877443033078388075 79033718816164549617582113)
    ·
      refine ⟨59275289112123412213186585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79033718816164549617582113 59275289112123412213186585)
      ·
        refine ⟨44456466834092559159889939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59275289112123412213186585 44456466834092559159889939)
        ·
          refine ⟨66684700251138838739834909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44456466834092559159889939 66684700251138838739834909)
          ·
            refine ⟨25006762594177064527438091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66684700251138838739834909 25006762594177064527438091)
            ·
              refine ⟨37510143891265596791157137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25006762594177064527438091 37510143891265596791157137)
              ·
                refine ⟨28132607918449197593367853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37510143891265596791157137 28132607918449197593367853)
                ·
                  refine ⟨10549727969418449097512945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28132607918449197593367853 10549727969418449097512945)
                  ·
                    refine ⟨7912295977063836823134709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10549727969418449097512945 7912295977063836823134709)
                    ·
                      refine ⟨741777747849734702168879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7912295977063836823134709 741777747849734702168879)
                      ·
                        rfl

theorem cell23_1444607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 2, 5].length) (baseStart_1444607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1444607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1444607 prefixEnd_1444607 := by exact prefixLift 1444607
  have htrace : WordTrace (prefixWord ++ tailWord_1444607) baseStart_1444607 baseEnd_1444607 := by
    simpa [prefixWord, tailWord_1444607, baseEnd_1444607] using wordTrace_append hprefix tailTrace_1444607
  have hstable : (prefixWord ++ tailWord_1444607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444607).length < 2 ^ (prefixWord ++ tailWord_1444607).sum := by decide
  have hdescent : baseEnd_1444607 < baseStart_1444607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444631 : List Nat := [1, 1, 3, 4, 3, 1, 1, 2, 2, 5]
def baseStart_1444631 : Nat := 118140960795 + 1444631 * 2 ^ 59
def prefixEnd_1444631 : Nat := 4983230072969 + 3 ^ 40 * 1444631 * 2
def baseEnd_1444631 : Nat := 247263357128480869422923

theorem tailTrace_1444631 : CollatzResearch.WordTrace tailWord_1444631 prefixEnd_1444631 247263357128480869422923 := by
  unfold tailWord_1444631
  simp only [CollatzResearch.WordTrace]
  refine ⟨52690021229356085177261747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35126680819570723451507831 52690021229356085177261747)
  ·
    refine ⟨79035031844034127765892621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52690021229356085177261747 79035031844034127765892621)
    ·
      refine ⟨29638136941512797912209733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79035031844034127765892621 29638136941512797912209733)
      ·
        refine ⟨5557150676533649608539325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29638136941512797912209733 5557150676533649608539325)
        ·
          refine ⟨2083931503700118603202247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5557150676533649608539325 2083931503700118603202247)
          ·
            refine ⟨3125897255550177904803371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2083931503700118603202247 3125897255550177904803371)
            ·
              refine ⟨4688845883325266857205057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3125897255550177904803371 4688845883325266857205057)
              ·
                refine ⟨3516634412493950142903793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4688845883325266857205057 3516634412493950142903793)
                ·
                  refine ⟨2637475809370462607177845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3516634412493950142903793 2637475809370462607177845)
                  ·
                    refine ⟨247263357128480869422923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2637475809370462607177845 247263357128480869422923)
                    ·
                      rfl

theorem cell23_1444631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 2, 2, 5].length) (baseStart_1444631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1444631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1444631 prefixEnd_1444631 := by exact prefixLift 1444631
  have htrace : WordTrace (prefixWord ++ tailWord_1444631) baseStart_1444631 baseEnd_1444631 := by
    simpa [prefixWord, tailWord_1444631, baseEnd_1444631] using wordTrace_append hprefix tailTrace_1444631
  have hstable : (prefixWord ++ tailWord_1444631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444631).length < 2 ^ (prefixWord ++ tailWord_1444631).sum := by decide
  have hdescent : baseEnd_1444631 < baseStart_1444631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444671 : List Nat := [1, 1, 2, 2, 5, 1, 1, 3, 2, 2, 3]
def baseStart_1444671 : Nat := 118140960795 + 1444671 * 2 ^ 59
def prefixEnd_1444671 : Nat := 4983230072969 + 3 ^ 40 * 1444671 * 2
def baseEnd_1444671 : Nat := 741810610611622451768585

theorem tailTrace_1444671 : CollatzResearch.WordTrace tailWord_1444671 prefixEnd_1444671 741810610611622451768585 := by
  unfold tailWord_1444671
  simp only [CollatzResearch.WordTrace]
  refine ⟨52691480149211172008717867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35127653432807448005811911 52691480149211172008717867)
  ·
    refine ⟨79037220223816758013076801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52691480149211172008717867 79037220223816758013076801)
    ·
      refine ⟨59277915167862568509807601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79037220223816758013076801 59277915167862568509807601)
      ·
        refine ⟨44458436375896926382355701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59277915167862568509807601 44458436375896926382355701)
        ·
          refine ⟨4167978410240336848345847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44458436375896926382355701 4167978410240336848345847)
          ·
            refine ⟨6251967615360505272518771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4167978410240336848345847 6251967615360505272518771)
            ·
              refine ⟨9377951423040757908778157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6251967615360505272518771 9377951423040757908778157)
              ·
                refine ⟨3516731783640284215791809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9377951423040757908778157 3516731783640284215791809)
                ·
                  refine ⟨2637548837730213161843857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3516731783640284215791809 2637548837730213161843857)
                  ·
                    refine ⟨1978161628297659871382893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2637548837730213161843857 1978161628297659871382893)
                    ·
                      refine ⟨741810610611622451768585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1978161628297659871382893 741810610611622451768585)
                      ·
                        rfl

theorem cell23_1444671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 3, 2, 2, 3].length) (baseStart_1444671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1444671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1444671 prefixEnd_1444671 := by exact prefixLift 1444671
  have htrace : WordTrace (prefixWord ++ tailWord_1444671) baseStart_1444671 baseEnd_1444671 := by
    simpa [prefixWord, tailWord_1444671, baseEnd_1444671] using wordTrace_append hprefix tailTrace_1444671
  have hstable : (prefixWord ++ tailWord_1444671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444671).length < 2 ^ (prefixWord ++ tailWord_1444671).sum := by decide
  have hdescent : baseEnd_1444671 < baseStart_1444671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444695 : List Nat := [1, 1, 3, 2, 4, 1, 4, 2, 1, 4]
def baseStart_1444695 : Nat := 118140960795 + 1444695 * 2 ^ 59
def prefixEnd_1444695 : Nat := 4983230072969 + 3 ^ 40 * 1444695 * 2
def baseEnd_1444695 : Nat := 247274311382443452622825

theorem tailTrace_1444695 : CollatzResearch.WordTrace tailWord_1444695 prefixEnd_1444695 247274311382443452622825 := by
  unfold tailWord_1444695
  simp only [CollatzResearch.WordTrace]
  refine ⟨52692355501124224107591539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35128237000749482738394359 52692355501124224107591539)
  ·
    refine ⟨79038533251686336161387309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52692355501124224107591539 79038533251686336161387309)
    ·
      refine ⟨29639449969382376060520241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79038533251686336161387309 29639449969382376060520241)
      ·
        refine ⟨22229587477036782045390181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29639449969382376060520241 22229587477036782045390181)
        ·
          refine ⟨4168047651944396633510659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22229587477036782045390181 4168047651944396633510659)
          ·
            refine ⟨6252071477916594950265989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4168047651944396633510659 6252071477916594950265989)
            ·
              refine ⟨1172263402109361553174873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6252071477916594950265989 1172263402109361553174873)
              ·
                refine ⟨879197551582021164881155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1172263402109361553174873 879197551582021164881155)
                ·
                  refine ⟨1318796327373031747321733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 879197551582021164881155 1318796327373031747321733)
                  ·
                    refine ⟨247274311382443452622825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1318796327373031747321733 247274311382443452622825)
                    ·
                      rfl

theorem cell23_1444695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 4, 2, 1, 4].length) (baseStart_1444695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1444695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1444695 prefixEnd_1444695 := by exact prefixLift 1444695
  have htrace : WordTrace (prefixWord ++ tailWord_1444695) baseStart_1444695 baseEnd_1444695 := by
    simpa [prefixWord, tailWord_1444695, baseEnd_1444695] using wordTrace_append hprefix tailTrace_1444695
  have hstable : (prefixWord ++ tailWord_1444695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444695).length < 2 ^ (prefixWord ++ tailWord_1444695).sum := by decide
  have hdescent : baseEnd_1444695 < baseStart_1444695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444704 : List Nat := [2, 1, 1, 3, 3, 1, 1, 1, 5, 5]
def baseStart_1444704 : Nat := 118140960795 + 1444704 * 2 ^ 59
def prefixEnd_1444704 : Nat := 4983230072969 + 3 ^ 40 * 1444704 * 2
def baseEnd_1444704 : Nat := 247275851824406940885311

theorem tailTrace_1444704 : CollatzResearch.WordTrace tailWord_1444704 prefixEnd_1444704 247275851824406940885311 := by
  unfold tailWord_1444704
  simp only [CollatzResearch.WordTrace]
  refine ⟨26346341879045809322334583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35128455838727745763112777 26346341879045809322334583)
  ·
    refine ⟨39519512818568713983501875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26346341879045809322334583 39519512818568713983501875)
    ·
      refine ⟨59279269227853070975252813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39519512818568713983501875 59279269227853070975252813)
      ·
        refine ⟨22229725960444901615719805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59279269227853070975252813 22229725960444901615719805)
        ·
          refine ⟨8336147235166838105894927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22229725960444901615719805 8336147235166838105894927)
          ·
            refine ⟨12504220852750257158842391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8336147235166838105894927 12504220852750257158842391)
            ·
              refine ⟨18756331279125385738263587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12504220852750257158842391 18756331279125385738263587)
              ·
                refine ⟨28134496918688078607395381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18756331279125385738263587 28134496918688078607395381)
                ·
                  refine ⟨2637609086127007369443317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28134496918688078607395381 2637609086127007369443317)
                  ·
                    refine ⟨247275851824406940885311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2637609086127007369443317 247275851824406940885311)
                    ·
                      rfl

theorem cell23_1444704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 5, 5].length) (baseStart_1444704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1444704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1444704 prefixEnd_1444704 := by exact prefixLift 1444704
  have htrace : WordTrace (prefixWord ++ tailWord_1444704) baseStart_1444704 baseEnd_1444704 := by
    simpa [prefixWord, tailWord_1444704, baseEnd_1444704] using wordTrace_append hprefix tailTrace_1444704
  have hstable : (prefixWord ++ tailWord_1444704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444704).length < 2 ^ (prefixWord ++ tailWord_1444704).sum := by decide
  have hdescent : baseEnd_1444704 < baseStart_1444704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444771 : List Nat := [1, 1, 1, 4, 1, 2, 5, 1, 1, 2, 4]
def baseStart_1444771 : Nat := 118140960795 + 1444771 * 2 ^ 59
def prefixEnd_1444771 : Nat := 4983230072969 + 3 ^ 40 * 1444771 * 2
def baseEnd_1444771 : Nat := 741861958677072060518125

theorem tailTrace_1444771 : CollatzResearch.WordTrace tailWord_1444771 prefixEnd_1444771 741861958677072060518125 := by
  unfold tailWord_1444771
  simp only [CollatzResearch.WordTrace]
  refine ⟨52695127448848889087358167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35130084965899259391572111 52695127448848889087358167)
  ·
    refine ⟨79042691173273333631037251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52695127448848889087358167 79042691173273333631037251)
    ·
      refine ⟨118564036759910000446555877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79042691173273333631037251 118564036759910000446555877)
      ·
        refine ⟨22230756892483125083729227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118564036759910000446555877 22230756892483125083729227)
        ·
          refine ⟨33346135338724687625593841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22230756892483125083729227 33346135338724687625593841)
          ·
            refine ⟨25009601504043515719195381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33346135338724687625593841 25009601504043515719195381)
            ·
              refine ⟨2344650141004079598674567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25009601504043515719195381 2344650141004079598674567)
              ·
                refine ⟨3516975211506119398011851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2344650141004079598674567 3516975211506119398011851)
                ·
                  refine ⟨5275462817259179097017777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3516975211506119398011851 5275462817259179097017777)
                  ·
                    refine ⟨3956597112944384322763333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5275462817259179097017777 3956597112944384322763333)
                    ·
                      refine ⟨741861958677072060518125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3956597112944384322763333 741861958677072060518125)
                      ·
                        rfl

theorem cell23_1444771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 1, 1, 2, 4].length) (baseStart_1444771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1444771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1444771 prefixEnd_1444771 := by exact prefixLift 1444771
  have htrace : WordTrace (prefixWord ++ tailWord_1444771) baseStart_1444771 baseEnd_1444771 := by
    simpa [prefixWord, tailWord_1444771, baseEnd_1444771] using wordTrace_append hprefix tailTrace_1444771
  have hstable : (prefixWord ++ tailWord_1444771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444771).length < 2 ^ (prefixWord ++ tailWord_1444771).sum := by decide
  have hdescent : baseEnd_1444771 < baseStart_1444771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444775 : List Nat := [1, 1, 6, 1, 3, 1, 2, 2, 1, 1, 4]
def baseStart_1444775 : Nat := 118140960795 + 1444775 * 2 ^ 59
def prefixEnd_1444775 : Nat := 4983230072969 + 3 ^ 40 * 1444775 * 2
def baseEnd_1444775 : Nat := 741864012599690044868107

theorem tailTrace_1444775 : CollatzResearch.WordTrace tailWord_1444775 prefixEnd_1444775 741864012599690044868107 := by
  unfold tailWord_1444775
  simp only [CollatzResearch.WordTrace]
  refine ⟨52695273340834397770503779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35130182227222931847002519 52695273340834397770503779)
  ·
    refine ⟨79042910011251596655755669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52695273340834397770503779 79042910011251596655755669)
    ·
      refine ⟨3705136406777418593238547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 79042910011251596655755669 3705136406777418593238547)
      ·
        refine ⟨5557704610166127889857821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3705136406777418593238547 5557704610166127889857821)
        ·
          refine ⟨2084139228812297958696683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5557704610166127889857821 2084139228812297958696683)
          ·
            refine ⟨3126208843218446938045025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2084139228812297958696683 3126208843218446938045025)
            ·
              refine ⟨2344656632413835203533769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3126208843218446938045025 2344656632413835203533769)
              ·
                refine ⟨1758492474310376402650327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2344656632413835203533769 1758492474310376402650327)
                ·
                  refine ⟨2637738711465564603975491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1758492474310376402650327 2637738711465564603975491)
                  ·
                    refine ⟨3956608067198346905963237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2637738711465564603975491 3956608067198346905963237)
                    ·
                      refine ⟨741864012599690044868107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3956608067198346905963237 741864012599690044868107)
                      ·
                        rfl

theorem cell23_1444775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_1444775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1444775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1444775 prefixEnd_1444775 := by exact prefixLift 1444775
  have htrace : WordTrace (prefixWord ++ tailWord_1444775) baseStart_1444775 baseEnd_1444775 := by
    simpa [prefixWord, tailWord_1444775, baseEnd_1444775] using wordTrace_append hprefix tailTrace_1444775
  have hstable : (prefixWord ++ tailWord_1444775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444775).length < 2 ^ (prefixWord ++ tailWord_1444775).sum := by decide
  have hdescent : baseEnd_1444775 < baseStart_1444775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444791 : List Nat := [1, 1, 3, 1, 3, 1, 2, 4, 1, 3, 3]
def baseStart_1444791 : Nat := 118140960795 + 1444791 * 2 ^ 59
def prefixEnd_1444791 : Nat := 4983230072969 + 3 ^ 40 * 1444791 * 2
def baseEnd_1444791 : Nat := 741872228290161982268033

theorem tailTrace_1444791 : CollatzResearch.WordTrace tailWord_1444791 prefixEnd_1444791 741872228290161982268033 := by
  unfold tailWord_1444791
  simp only [CollatzResearch.WordTrace]
  refine ⟨52695856908776432503086227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35130571272517621668724151 52695856908776432503086227)
  ·
    refine ⟨79043785363164648754629341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52695856908776432503086227 79043785363164648754629341)
    ·
      refine ⟨29641419511186743282986003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79043785363164648754629341 29641419511186743282986003)
      ·
        refine ⟨44462129266780114924479005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29641419511186743282986003 44462129266780114924479005)
        ·
          refine ⟨16673298475042543096679627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44462129266780114924479005 16673298475042543096679627)
          ·
            refine ⟨25009947712563814645019441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16673298475042543096679627 25009947712563814645019441)
            ·
              refine ⟨18757460784422860983764581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25009947712563814645019441 18757460784422860983764581)
              ·
                refine ⟨3517023897079286434455859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18757460784422860983764581 3517023897079286434455859)
                ·
                  refine ⟨5275535845618929651683789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3517023897079286434455859 5275535845618929651683789)
                  ·
                    refine ⟨1978325942107098619381421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5275535845618929651683789 1978325942107098619381421)
                    ·
                      refine ⟨741872228290161982268033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1978325942107098619381421 741872228290161982268033)
                      ·
                        rfl

theorem cell23_1444791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 4, 1, 3, 3].length) (baseStart_1444791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1444791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1444791 prefixEnd_1444791 := by exact prefixLift 1444791
  have htrace : WordTrace (prefixWord ++ tailWord_1444791) baseStart_1444791 baseEnd_1444791 := by
    simpa [prefixWord, tailWord_1444791, baseEnd_1444791] using wordTrace_append hprefix tailTrace_1444791
  have hstable : (prefixWord ++ tailWord_1444791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444791).length < 2 ^ (prefixWord ++ tailWord_1444791).sum := by decide
  have hdescent : baseEnd_1444791 < baseStart_1444791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444792 : List Nat := [2, 1, 2, 1, 2, 4, 3, 3, 1, 2, 2]
def baseStart_1444792 : Nat := 118140960795 + 1444792 * 2 ^ 59
def prefixEnd_1444792 : Nat := 4983230072969 + 3 ^ 40 * 1444792 * 2
def baseEnd_1444792 : Nat := 741872741770816478355529

theorem tailTrace_1444792 : CollatzResearch.WordTrace tailWord_1444792 prefixEnd_1444792 741872741770816478355529 := by
  unfold tailWord_1444792
  simp only [CollatzResearch.WordTrace]
  refine ⟨26347946690886404836936315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35130595587848539782581753 26347946690886404836936315)
  ·
    refine ⟨39521920036329607255404473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26347946690886404836936315 39521920036329607255404473)
    ·
      refine ⟨29641440027247205441553355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39521920036329607255404473 29641440027247205441553355)
      ·
        refine ⟨44462160040870808162330033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29641440027247205441553355 44462160040870808162330033)
        ·
          refine ⟨33346620030653106121747525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44462160040870808162330033 33346620030653106121747525)
          ·
            refine ⟨6252491255747457397827661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33346620030653106121747525 6252491255747457397827661)
            ·
              refine ⟨2344684220905296524185373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6252491255747457397827661 2344684220905296524185373)
              ·
                refine ⟨879256582839486196569515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2344684220905296524185373 879256582839486196569515)
                ·
                  refine ⟨1318884874259229294854273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 879256582839486196569515 1318884874259229294854273)
                  ·
                    refine ⟨989163655694421971140705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1318884874259229294854273 989163655694421971140705)
                    ·
                      refine ⟨741872741770816478355529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 989163655694421971140705 741872741770816478355529)
                      ·
                        rfl

theorem cell23_1444792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 3, 1, 2, 2].length) (baseStart_1444792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1444792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1444792 prefixEnd_1444792 := by exact prefixLift 1444792
  have htrace : WordTrace (prefixWord ++ tailWord_1444792) baseStart_1444792 baseEnd_1444792 := by
    simpa [prefixWord, tailWord_1444792, baseEnd_1444792] using wordTrace_append hprefix tailTrace_1444792
  have hstable : (prefixWord ++ tailWord_1444792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444792).length < 2 ^ (prefixWord ++ tailWord_1444792).sum := by decide
  have hdescent : baseEnd_1444792 < baseStart_1444792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444825 : List Nat := [1, 2, 1, 2, 5, 2, 1, 3, 2, 1, 3]
def baseStart_1444825 : Nat := 118140960795 + 1444825 * 2 ^ 59
def prefixEnd_1444825 : Nat := 4983230072969 + 3 ^ 40 * 1444825 * 2
def baseEnd_1444825 : Nat := 741889686632414849242877

theorem tailTrace_1444825 : CollatzResearch.WordTrace tailWord_1444825 prefixEnd_1444825 741889686632414849242877 := by
  unfold tailWord_1444825
  simp only [CollatzResearch.WordTrace]
  refine ⟨52697096990653256309823929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35131397993768837539882619 52697096990653256309823929)
  ·
    refine ⟨39522822742989942232367947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52697096990653256309823929 39522822742989942232367947)
    ·
      refine ⟨59284234114484913348551921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39522822742989942232367947 59284234114484913348551921)
      ·
        refine ⟨44463175585863685011413941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59284234114484913348551921 44463175585863685011413941)
        ·
          refine ⟨4168422711174720469820057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44463175585863685011413941 4168422711174720469820057)
          ·
            refine ⟨3126317033381040352365043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4168422711174720469820057 3126317033381040352365043)
            ·
              refine ⟨4689475550071560528547565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3126317033381040352365043 4689475550071560528547565)
              ·
                refine ⟨1758553331276835198205337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4689475550071560528547565 1758553331276835198205337)
                ·
                  refine ⟨1318914998457626398654003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1758553331276835198205337 1318914998457626398654003)
                  ·
                    refine ⟨1978372497686439597981005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1318914998457626398654003 1978372497686439597981005)
                    ·
                      refine ⟨741889686632414849242877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1978372497686439597981005 741889686632414849242877)
                      ·
                        rfl

theorem cell23_1444825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 3, 2, 1, 3].length) (baseStart_1444825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1444825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1444825 prefixEnd_1444825 := by exact prefixLift 1444825
  have htrace : WordTrace (prefixWord ++ tailWord_1444825) baseStart_1444825 baseEnd_1444825 := by
    simpa [prefixWord, tailWord_1444825, baseEnd_1444825] using wordTrace_append hprefix tailTrace_1444825
  have hstable : (prefixWord ++ tailWord_1444825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444825).length < 2 ^ (prefixWord ++ tailWord_1444825).sum := by decide
  have hdescent : baseEnd_1444825 < baseStart_1444825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444861 : List Nat := [1, 4, 1, 1, 1, 2, 1, 4, 2, 2, 4]
def baseStart_1444861 : Nat := 118140960795 + 1444861 * 2 ^ 59
def prefixEnd_1444861 : Nat := 4983230072969 + 3 ^ 40 * 1444861 * 2
def baseEnd_1444861 : Nat := 741908171935976708392711

theorem tailTrace_1444861 : CollatzResearch.WordTrace tailWord_1444861 prefixEnd_1444861 741908171935976708392711 := by
  unfold tailWord_1444861
  simp only [CollatzResearch.WordTrace]
  refine ⟨52698410018522834458134437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35132273345681889638756291 52698410018522834458134437)
  ·
    refine ⟨9880951878473031460900207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52698410018522834458134437 9880951878473031460900207)
    ·
      refine ⟨14821427817709547191350311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9880951878473031460900207 14821427817709547191350311)
      ·
        refine ⟨22232141726564320787025467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14821427817709547191350311 22232141726564320787025467)
        ·
          refine ⟨33348212589846481180538201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22232141726564320787025467 33348212589846481180538201)
          ·
            refine ⟨25011159442384860885403651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33348212589846481180538201 25011159442384860885403651)
            ·
              refine ⟨37516739163577291328105477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25011159442384860885403651 37516739163577291328105477)
              ·
                refine ⟨7034388593170742124019777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37516739163577291328105477 7034388593170742124019777)
                ·
                  refine ⟨5275791444878056593014833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7034388593170742124019777 5275791444878056593014833)
                  ·
                    refine ⟨3956843583658542444761125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5275791444878056593014833 3956843583658542444761125)
                    ·
                      refine ⟨741908171935976708392711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3956843583658542444761125 741908171935976708392711)
                      ·
                        rfl

theorem cell23_1444861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 2, 2, 4].length) (baseStart_1444861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1444861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1444861 prefixEnd_1444861 := by exact prefixLift 1444861
  have htrace : WordTrace (prefixWord ++ tailWord_1444861) baseStart_1444861 baseEnd_1444861 := by
    simpa [prefixWord, tailWord_1444861, baseEnd_1444861] using wordTrace_append hprefix tailTrace_1444861
  have hstable : (prefixWord ++ tailWord_1444861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444861).length < 2 ^ (prefixWord ++ tailWord_1444861).sum := by decide
  have hdescent : baseEnd_1444861 < baseStart_1444861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444871 : List Nat := [1, 1, 4, 3, 1, 1, 2, 3, 7]
def baseStart_1444871 : Nat := 118140960795 + 1444871 * 2 ^ 59
def prefixEnd_1444871 : Nat := 4983230072969 + 3 ^ 40 * 1444871 * 2
def baseEnd_1444871 : Nat := 82434811860280185474185

theorem tailTrace_1444871 : CollatzResearch.WordTrace tailWord_1444871 prefixEnd_1444871 82434811860280185474185 := by
  unfold tailWord_1444871
  simp only [CollatzResearch.WordTrace]
  refine ⟨52698774748486606165998467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35132516498991070777332311 52698774748486606165998467)
  ·
    refine ⟨79048162122729909248997701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52698774748486606165998467 79048162122729909248997701)
    ·
      refine ⟨14821530398011857984187069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79048162122729909248997701 14821530398011857984187069)
      ·
        refine ⟨5558073899254446744070151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14821530398011857984187069 5558073899254446744070151)
        ·
          refine ⟨8337110848881670116105227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5558073899254446744070151 8337110848881670116105227)
          ·
            refine ⟨12505666273322505174157841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8337110848881670116105227 12505666273322505174157841)
            ·
              refine ⟨9379249704991878880618381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12505666273322505174157841 9379249704991878880618381)
              ·
                refine ⟨3517218639371954580231893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9379249704991878880618381 3517218639371954580231893)
                ·
                  refine ⟨82434811860280185474185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3517218639371954580231893 82434811860280185474185)
                  ·
                    rfl

theorem cell23_1444871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 3, 7].length) (baseStart_1444871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1444871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1444871 prefixEnd_1444871 := by exact prefixLift 1444871
  have htrace : WordTrace (prefixWord ++ tailWord_1444871) baseStart_1444871 baseEnd_1444871 := by
    simpa [prefixWord, tailWord_1444871, baseEnd_1444871] using wordTrace_append hprefix tailTrace_1444871
  have hstable : (prefixWord ++ tailWord_1444871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444871).length < 2 ^ (prefixWord ++ tailWord_1444871).sum := by decide
  have hdescent : baseEnd_1444871 < baseStart_1444871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444878 : List Nat := [4, 1, 1, 2, 2, 3, 1, 1, 2, 2, 4]
def baseStart_1444878 : Nat := 118140960795 + 1444878 * 2 ^ 59
def prefixEnd_1444878 : Nat := 4983230072969 + 3 ^ 40 * 1444878 * 2
def baseEnd_1444878 : Nat := 741916901107103141880133

theorem tailTrace_1444878 : CollatzResearch.WordTrace tailWord_1444878 prefixEnd_1444878 741916901107103141880133 := by
  unfold tailWord_1444878
  simp only [CollatzResearch.WordTrace]
  refine ⟨6587378757432655795187911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35132686706307497574335525 6587378757432655795187911)
  ·
    refine ⟨9881068136148983692781867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6587378757432655795187911 9881068136148983692781867)
    ·
      refine ⟨14821602204223475539172801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9881068136148983692781867 14821602204223475539172801)
      ·
        refine ⟨11116201653167606654379601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14821602204223475539172801 11116201653167606654379601)
        ·
          refine ⟨8337151239875704990784701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11116201653167606654379601 8337151239875704990784701)
          ·
            refine ⟨3126431714953389371544263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8337151239875704990784701 3126431714953389371544263)
            ·
              refine ⟨4689647572430084057316395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3126431714953389371544263 4689647572430084057316395)
              ·
                refine ⟨7034471358645126085974593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4689647572430084057316395 7034471358645126085974593)
                ·
                  refine ⟨5275853518983844564480945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7034471358645126085974593 5275853518983844564480945)
                  ·
                    refine ⟨3956890139237883423360709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5275853518983844564480945 3956890139237883423360709)
                    ·
                      refine ⟨741916901107103141880133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3956890139237883423360709 741916901107103141880133)
                      ·
                        rfl

theorem cell23_1444878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_1444878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1444878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1444878 prefixEnd_1444878 := by exact prefixLift 1444878
  have htrace : WordTrace (prefixWord ++ tailWord_1444878) baseStart_1444878 baseEnd_1444878 := by
    simpa [prefixWord, tailWord_1444878, baseEnd_1444878] using wordTrace_append hprefix tailTrace_1444878
  have hstable : (prefixWord ++ tailWord_1444878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444878).length < 2 ^ (prefixWord ++ tailWord_1444878).sum := by decide
  have hdescent : baseEnd_1444878 < baseStart_1444878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444901 : List Nat := [1, 3, 1, 2, 2, 2, 3, 1, 1, 7]
def baseStart_1444901 : Nat := 118140960795 + 1444901 * 2 ^ 59
def prefixEnd_1444901 : Nat := 4983230072969 + 3 ^ 40 * 1444901 * 2
def baseEnd_1444901 : Nat := 247309570387385517297509

theorem tailTrace_1444901 : CollatzResearch.WordTrace tailWord_1444901 prefixEnd_1444901 247309570387385517297509 := by
  unfold tailWord_1444901
  simp only [CollatzResearch.WordTrace]
  refine ⟨52699868938377921289590557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35133245958918614193060371 52699868938377921289590557)
  ·
    refine ⟨19762450851891720483596459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52699868938377921289590557 19762450851891720483596459)
    ·
      refine ⟨29643676277837580725394689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19762450851891720483596459 29643676277837580725394689)
      ·
        refine ⟨22232757208378185544046017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29643676277837580725394689 22232757208378185544046017)
        ·
          refine ⟨16674567906283639158034513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22232757208378185544046017 16674567906283639158034513)
          ·
            refine ⟨12505925929712729368525885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16674567906283639158034513 12505925929712729368525885)
            ·
              refine ⟨4689722223642273513197207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12505925929712729368525885 4689722223642273513197207)
              ·
                refine ⟨7034583335463410269795811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4689722223642273513197207 7034583335463410269795811)
                ·
                  refine ⟨10551875003195115404693717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7034583335463410269795811 10551875003195115404693717)
                  ·
                    refine ⟨247309570387385517297509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10551875003195115404693717 247309570387385517297509)
                    ·
                      rfl

theorem cell23_1444901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 7].length) (baseStart_1444901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1444901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1444901 prefixEnd_1444901 := by exact prefixLift 1444901
  have htrace : WordTrace (prefixWord ++ tailWord_1444901) baseStart_1444901 baseEnd_1444901 := by
    simpa [prefixWord, tailWord_1444901, baseEnd_1444901] using wordTrace_append hprefix tailTrace_1444901
  have hstable : (prefixWord ++ tailWord_1444901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444901).length < 2 ^ (prefixWord ++ tailWord_1444901).sum := by decide
  have hdescent : baseEnd_1444901 < baseStart_1444901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444916 : List Nat := [2, 5, 1, 2, 1, 3, 1, 2, 2, 2, 2]
def baseStart_1444916 : Nat := 118140960795 + 1444916 * 2 ^ 59
def prefixEnd_1444916 : Nat := 4983230072969 + 3 ^ 40 * 1444916 * 2
def baseEnd_1444916 : Nat := 741936413371973993204959

theorem tailTrace_1444916 : CollatzResearch.WordTrace tailWord_1444916 prefixEnd_1444916 741936413371973993204959 := by
  unfold tailWord_1444916
  simp only [CollatzResearch.WordTrace]
  refine ⟨26350208016661789425693301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35133610688882385900924401 26350208016661789425693301)
  ·
    refine ⟨2470332001562042758658747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26350208016661789425693301 2470332001562042758658747)
    ·
      refine ⟨3705498002343064137988121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2470332001562042758658747 3705498002343064137988121)
      ·
        refine ⟨2779123501757298103491091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3705498002343064137988121 2779123501757298103491091)
        ·
          refine ⟨4168685252635947155236637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2779123501757298103491091 4168685252635947155236637)
          ·
            refine ⟨1563256969738480183213739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4168685252635947155236637 1563256969738480183213739)
            ·
              refine ⟨2344885454607720274820609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1563256969738480183213739 2344885454607720274820609)
              ·
                refine ⟨1758664090955790206115457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2344885454607720274820609 1758664090955790206115457)
                ·
                  refine ⟨1318998068216842654586593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1758664090955790206115457 1318998068216842654586593)
                  ·
                    refine ⟨989248551162631990939945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1318998068216842654586593 989248551162631990939945)
                    ·
                      refine ⟨741936413371973993204959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 989248551162631990939945 741936413371973993204959)
                      ·
                        rfl

theorem cell23_1444916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_1444916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1444916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1444916 prefixEnd_1444916 := by exact prefixLift 1444916
  have htrace : WordTrace (prefixWord ++ tailWord_1444916) baseStart_1444916 baseEnd_1444916 := by
    simpa [prefixWord, tailWord_1444916, baseEnd_1444916] using wordTrace_append hprefix tailTrace_1444916
  have hstable : (prefixWord ++ tailWord_1444916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444916).length < 2 ^ (prefixWord ++ tailWord_1444916).sum := by decide
  have hdescent : baseEnd_1444916 < baseStart_1444916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444951 : List Nat := [1, 1, 3, 2, 2, 1, 1, 1, 1, 6, 4]
def baseStart_1444951 : Nat := 118140960795 + 1444951 * 2 ^ 59
def prefixEnd_1444951 : Nat := 4983230072969 + 3 ^ 40 * 1444951 * 2
def baseEnd_1444951 : Nat := 741954385194881356267297

theorem tailTrace_1444951 : CollatzResearch.WordTrace tailWord_1444951 prefixEnd_1444951 741954385194881356267297 := by
  unfold tailWord_1444951
  simp only [CollatzResearch.WordTrace]
  refine ⟨52701692588196779828910707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35134461725464519885940471 52701692588196779828910707)
  ·
    refine ⟨79052538882295169743366061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52701692588196779828910707 79052538882295169743366061)
    ·
      refine ⟨29644702080860688653762273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79052538882295169743366061 29644702080860688653762273)
      ·
        refine ⟨22233526560645516490321705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29644702080860688653762273 22233526560645516490321705)
        ·
          refine ⟨16675144920484137367741279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22233526560645516490321705 16675144920484137367741279)
          ·
            refine ⟨25012717380726206051611919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16675144920484137367741279 25012717380726206051611919)
            ·
              refine ⟨37519076071089309077417879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25012717380726206051611919 37519076071089309077417879)
              ·
                refine ⟨56278614106633963616126819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37519076071089309077417879 56278614106633963616126819)
                ·
                  refine ⟨84417921159950945424190229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56278614106633963616126819 84417921159950945424190229)
                  ·
                    refine ⟨3957090054372700566758917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 84417921159950945424190229 3957090054372700566758917)
                    ·
                      refine ⟨741954385194881356267297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3957090054372700566758917 741954385194881356267297)
                      ·
                        rfl

theorem cell23_1444951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 6, 4].length) (baseStart_1444951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1444951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1444951 prefixEnd_1444951 := by exact prefixLift 1444951
  have htrace : WordTrace (prefixWord ++ tailWord_1444951) baseStart_1444951 baseEnd_1444951 := by
    simpa [prefixWord, tailWord_1444951, baseEnd_1444951] using wordTrace_append hprefix tailTrace_1444951
  have hstable : (prefixWord ++ tailWord_1444951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444951).length < 2 ^ (prefixWord ++ tailWord_1444951).sum := by decide
  have hdescent : baseEnd_1444951 < baseStart_1444951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444961 : List Nat := [1, 2, 3, 1, 1, 2, 3, 2, 8]
def baseStart_1444961 : Nat := 118140960795 + 1444961 * 2 ^ 59
def prefixEnd_1444961 : Nat := 4983230072969 + 3 ^ 40 * 1444961 * 2
def baseEnd_1444961 : Nat := 82439946666825146349139

theorem tailTrace_1444961 : CollatzResearch.WordTrace tailWord_1444961 prefixEnd_1444961 82439946666825146349139 := by
  unfold tailWord_1444961
  simp only [CollatzResearch.WordTrace]
  refine ⟨52702057318160551536774737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35134704878773701024516491 52702057318160551536774737)
  ·
    refine ⟨39526542988620413652581053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52702057318160551536774737 39526542988620413652581053)
    ·
      refine ⟨14822453620732655119717895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39526542988620413652581053 14822453620732655119717895)
      ·
        refine ⟨22233680431098982679576843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14822453620732655119717895 22233680431098982679576843)
        ·
          refine ⟨33350520646648474019365265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22233680431098982679576843 33350520646648474019365265)
          ·
            refine ⟨25012890484986355514523949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33350520646648474019365265 25012890484986355514523949)
            ·
              refine ⟨9379833931869883317946481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25012890484986355514523949 9379833931869883317946481)
              ·
                refine ⟨7034875448902412488459861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9379833931869883317946481 7034875448902412488459861)
                ·
                  refine ⟨82439946666825146349139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7034875448902412488459861 82439946666825146349139)
                  ·
                    rfl

theorem cell23_1444961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 8].length) (baseStart_1444961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1444961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1444961 prefixEnd_1444961 := by exact prefixLift 1444961
  have htrace : WordTrace (prefixWord ++ tailWord_1444961) baseStart_1444961 baseEnd_1444961 := by
    simpa [prefixWord, tailWord_1444961, baseEnd_1444961] using wordTrace_append hprefix tailTrace_1444961
  have hstable : (prefixWord ++ tailWord_1444961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444961).length < 2 ^ (prefixWord ++ tailWord_1444961).sum := by decide
  have hdescent : baseEnd_1444961 < baseStart_1444961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444978 : List Nat := [3, 2, 1, 2, 2, 1, 2, 4, 6]
def baseStart_1444978 : Nat := 118140960795 + 1444978 * 2 ^ 59
def prefixEnd_1444978 : Nat := 4983230072969 + 3 ^ 40 * 1444978 * 2
def baseEnd_1444978 : Nat := 82440916574728083403297

theorem tailTrace_1444978 : CollatzResearch.WordTrace tailWord_1444978 prefixEnd_1444978 82440916574728083403297 := by
  unfold tailWord_1444978
  simp only [CollatzResearch.WordTrace]
  refine ⟨13175669339774740860035897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35135118239399308960095725 13175669339774740860035897)
  ·
    refine ⟨9881752004831055645026923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13175669339774740860035897 9881752004831055645026923)
    ·
      refine ⟨14822628007246583467540385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9881752004831055645026923 14822628007246583467540385)
      ·
        refine ⟨11116971005434937600655289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14822628007246583467540385 11116971005434937600655289)
        ·
          refine ⟨8337728254076203200491467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11116971005434937600655289 8337728254076203200491467)
          ·
            refine ⟨12506592381114304800737201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8337728254076203200491467 12506592381114304800737201)
            ·
              refine ⟨9379944285835728600552901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12506592381114304800737201 9379944285835728600552901)
              ·
                refine ⟨1758739553594199112603669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9379944285835728600552901 1758739553594199112603669)
                ·
                  refine ⟨82440916574728083403297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1758739553594199112603669 82440916574728083403297)
                  ·
                    rfl

theorem cell23_1444978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 4, 6].length) (baseStart_1444978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1444978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1444978 prefixEnd_1444978 := by exact prefixLift 1444978
  have htrace : WordTrace (prefixWord ++ tailWord_1444978) baseStart_1444978 baseEnd_1444978 := by
    simpa [prefixWord, tailWord_1444978, baseEnd_1444978] using wordTrace_append hprefix tailTrace_1444978
  have hstable : (prefixWord ++ tailWord_1444978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444978).length < 2 ^ (prefixWord ++ tailWord_1444978).sum := by decide
  have hdescent : baseEnd_1444978 < baseStart_1444978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445008 : List Nat := [2, 1, 1, 1, 1, 1, 4, 6, 1, 5]
def baseStart_1445008 : Nat := 118140960795 + 1445008 * 2 ^ 59
def prefixEnd_1445008 : Nat := 4983230072969 + 3 ^ 40 * 1445008 * 2
def baseEnd_1445008 : Nat := 247327884530729211084845

theorem tailTrace_1445008 : CollatzResearch.WordTrace tailWord_1445008 prefixEnd_1445008 247327884530729211084845 := by
  unfold tailWord_1445008
  simp only [CollatzResearch.WordTrace]
  refine ⟨26351885774495139281867839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35135847699326852375823785 26351885774495139281867839)
  ·
    refine ⟨39527828661742708922801759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26351885774495139281867839 39527828661742708922801759)
    ·
      refine ⟨59291742992614063384202639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39527828661742708922801759 59291742992614063384202639)
      ·
        refine ⟨88937614488921095076303959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59291742992614063384202639 88937614488921095076303959)
        ·
          refine ⟨133406421733381642614455939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88937614488921095076303959 133406421733381642614455939)
          ·
            refine ⟨200109632600072463921683909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133406421733381642614455939 200109632600072463921683909)
            ·
              refine ⟨37520556112513586985315733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 200109632600072463921683909 37520556112513586985315733)
              ·
                refine ⟨1758776067774074389936675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 37520556112513586985315733 1758776067774074389936675)
                ·
                  refine ⟨2638164101661111584905013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1758776067774074389936675 2638164101661111584905013)
                  ·
                    refine ⟨247327884530729211084845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2638164101661111584905013 247327884530729211084845)
                    ·
                      rfl

theorem cell23_1445008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 6, 1, 5].length) (baseStart_1445008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1445008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1445008 prefixEnd_1445008 := by exact prefixLift 1445008
  have htrace : WordTrace (prefixWord ++ tailWord_1445008) baseStart_1445008 baseEnd_1445008 := by
    simpa [prefixWord, tailWord_1445008, baseEnd_1445008] using wordTrace_append hprefix tailTrace_1445008
  have hstable : (prefixWord ++ tailWord_1445008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445008).length < 2 ^ (prefixWord ++ tailWord_1445008).sum := by decide
  have hdescent : baseEnd_1445008 < baseStart_1445008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445039 : List Nat := [1, 1, 2, 1, 2, 3, 6, 2, 1, 1, 3]
def baseStart_1445039 : Nat := 118140960795 + 1445039 * 2 ^ 59
def prefixEnd_1445039 : Nat := 4983230072969 + 3 ^ 40 * 1445039 * 2
def baseEnd_1445039 : Nat := 741999571492477011966893

theorem tailTrace_1445039 : CollatzResearch.WordTrace tailWord_1445039 prefixEnd_1445039 741999571492477011966893 := by
  unfold tailWord_1445039
  simp only [CollatzResearch.WordTrace]
  refine ⟨52704902211877970858114171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35136601474585313905409447 52704902211877970858114171)
  ·
    refine ⟨79057353317816956287171257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52704902211877970858114171 79057353317816956287171257)
    ·
      refine ⟨59293014988362717215378443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79057353317816956287171257 59293014988362717215378443)
      ·
        refine ⟨88939522482544075823067665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59293014988362717215378443 88939522482544075823067665)
        ·
          refine ⟨66704641861908056867300749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88939522482544075823067665 66704641861908056867300749)
          ·
            refine ⟨25014240698215521325237781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66704641861908056867300749 25014240698215521325237781)
            ·
              refine ⟨1172542532728852562120521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 25014240698215521325237781 1172542532728852562120521)
              ·
                refine ⟨879406899546639421590391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1172542532728852562120521 879406899546639421590391)
                ·
                  refine ⟨1319110349319959132385587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 879406899546639421590391 1319110349319959132385587)
                  ·
                    refine ⟨1978665523979938698578381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1319110349319959132385587 1978665523979938698578381)
                    ·
                      refine ⟨741999571492477011966893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1978665523979938698578381 741999571492477011966893)
                      ·
                        rfl

theorem cell23_1445039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 6, 2, 1, 1, 3].length) (baseStart_1445039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1445039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1445039 prefixEnd_1445039 := by exact prefixLift 1445039
  have htrace : WordTrace (prefixWord ++ tailWord_1445039) baseStart_1445039 baseEnd_1445039 := by
    simpa [prefixWord, tailWord_1445039, baseEnd_1445039] using wordTrace_append hprefix tailTrace_1445039
  have hstable : (prefixWord ++ tailWord_1445039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445039).length < 2 ^ (prefixWord ++ tailWord_1445039).sum := by decide
  have hdescent : baseEnd_1445039 < baseStart_1445039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445051 : List Nat := [1, 1, 1, 1, 1, 2, 4, 12]
def baseStart_1445051 : Nat := 118140960795 + 1445051 * 2 ^ 59
def prefixEnd_1445051 : Nat := 4983230072969 + 3 ^ 40 * 1445051 * 2
def baseEnd_1445051 : Nat := 27481693824456702408031

theorem tailTrace_1445051 : CollatzResearch.WordTrace tailWord_1445051 prefixEnd_1445051 27481693824456702408031 := by
  unfold tailWord_1445051
  simp only [CollatzResearch.WordTrace]
  refine ⟨52705339887834496907551007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35136893258556331271700671 52705339887834496907551007)
  ·
    refine ⟨79058009831751745361326511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52705339887834496907551007 79058009831751745361326511)
    ·
      refine ⟨118587014747627618041989767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79058009831751745361326511 118587014747627618041989767)
      ·
        refine ⟨177880522121441427062984651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118587014747627618041989767 177880522121441427062984651)
        ·
          refine ⟨266820783182162140594476977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177880522121441427062984651 266820783182162140594476977)
          ·
            refine ⟨200115587386621605445857733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 266820783182162140594476977 200115587386621605445857733)
            ·
              refine ⟨37521672634991551021098325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 200115587386621605445857733 37521672634991551021098325)
              ·
                refine ⟨27481693824456702408031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 37521672634991551021098325 27481693824456702408031)
                ·
                  rfl

theorem cell23_1445051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 12].length) (baseStart_1445051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1445051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1445051 prefixEnd_1445051 := by exact prefixLift 1445051
  have htrace : WordTrace (prefixWord ++ tailWord_1445051) baseStart_1445051 baseEnd_1445051 := by
    simpa [prefixWord, tailWord_1445051, baseEnd_1445051] using wordTrace_append hprefix tailTrace_1445051
  have hstable : (prefixWord ++ tailWord_1445051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445051).length < 2 ^ (prefixWord ++ tailWord_1445051).sum := by decide
  have hdescent : baseEnd_1445051 < baseStart_1445051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445055 : List Nat := [1, 1, 2, 2, 2, 2, 4, 3, 2, 4]
def baseStart_1445055 : Nat := 118140960795 + 1445055 * 2 ^ 59
def prefixEnd_1445055 : Nat := 4983230072969 + 3 ^ 40 * 1445055 * 2
def baseEnd_1445055 : Nat := 247335929060982983122273

theorem tailTrace_1445055 : CollatzResearch.WordTrace tailWord_1445055 prefixEnd_1445055 247335929060982983122273 := by
  unfold tailWord_1445055
  simp only [CollatzResearch.WordTrace]
  refine ⟨52705485779820005590696619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35136990519880003727131079 52705485779820005590696619)
  ·
    refine ⟨79058228669730008386044929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52705485779820005590696619 79058228669730008386044929)
    ·
      refine ⟨59293671502297506289533697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79058228669730008386044929 59293671502297506289533697)
      ·
        refine ⟨44470253626723129717150273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59293671502297506289533697 44470253626723129717150273)
        ·
          refine ⟨33352690220042347287862705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44470253626723129717150273 33352690220042347287862705)
          ·
            refine ⟨25014517665031760465897029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33352690220042347287862705 25014517665031760465897029)
            ·
              refine ⟨4690222062193455087355693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25014517665031760465897029 4690222062193455087355693)
              ·
                refine ⟨1758833273322545657758385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4690222062193455087355693 1758833273322545657758385)
                ·
                  refine ⟨1319124954991909243318789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1758833273322545657758385 1319124954991909243318789)
                  ·
                    refine ⟨247335929060982983122273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1319124954991909243318789 247335929060982983122273)
                    ·
                      rfl

theorem cell23_1445055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 3, 2, 4].length) (baseStart_1445055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1445055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1445055 prefixEnd_1445055 := by exact prefixLift 1445055
  have htrace : WordTrace (prefixWord ++ tailWord_1445055) baseStart_1445055 baseEnd_1445055 := by
    simpa [prefixWord, tailWord_1445055, baseEnd_1445055] using wordTrace_append hprefix tailTrace_1445055
  have hstable : (prefixWord ++ tailWord_1445055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445055).length < 2 ^ (prefixWord ++ tailWord_1445055).sum := by decide
  have hdescent : baseEnd_1445055 < baseStart_1445055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445076 : List Nat := [2, 4, 1, 4, 1, 2, 2, 1, 1, 5]
def baseStart_1445076 : Nat := 118140960795 + 1445076 * 2 ^ 59
def prefixEnd_1445076 : Nat := 4983230072969 + 3 ^ 40 * 1445076 * 2
def baseEnd_1445076 : Nat := 247339523425564455734741

theorem tailTrace_1445076 : CollatzResearch.WordTrace tailWord_1445076 prefixEnd_1445076 247339523425564455734741 := by
  unfold tailWord_1445076
  simp only [CollatzResearch.WordTrace]
  refine ⟨26353125856371963088605541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35137501141829284118140721 26353125856371963088605541)
  ·
    refine ⟨4941211098069743079113539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26353125856371963088605541 4941211098069743079113539)
    ·
      refine ⟨7411816647104614618670309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4941211098069743079113539 7411816647104614618670309)
      ·
        refine ⟨1389715621332115241000683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7411816647104614618670309 1389715621332115241000683)
        ·
          refine ⟨2084573431998172861501025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1389715621332115241000683 2084573431998172861501025)
          ·
            refine ⟨1563430073998629646125769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2084573431998172861501025 1563430073998629646125769)
            ·
              refine ⟨1172572555498972234594327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1563430073998629646125769 1172572555498972234594327)
              ·
                refine ⟨1758858833248458351891491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1172572555498972234594327 1758858833248458351891491)
                ·
                  refine ⟨2638288249872687527837237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1758858833248458351891491 2638288249872687527837237)
                  ·
                    refine ⟨247339523425564455734741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2638288249872687527837237 247339523425564455734741)
                    ·
                      rfl

theorem cell23_1445076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 2, 1, 1, 5].length) (baseStart_1445076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1445076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1445076 prefixEnd_1445076 := by exact prefixLift 1445076
  have htrace : WordTrace (prefixWord ++ tailWord_1445076) baseStart_1445076 baseEnd_1445076 := by
    simpa [prefixWord, tailWord_1445076, baseEnd_1445076] using wordTrace_append hprefix tailTrace_1445076
  have hstable : (prefixWord ++ tailWord_1445076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445076).length < 2 ^ (prefixWord ++ tailWord_1445076).sum := by decide
  have hdescent : baseEnd_1445076 < baseStart_1445076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445079 : List Nat := [1, 1, 3, 2, 1, 2, 3, 5, 1, 2, 2]
def baseStart_1445079 : Nat := 118140960795 + 1445079 * 2 ^ 59
def prefixEnd_1445079 : Nat := 4983230072969 + 3 ^ 40 * 1445079 * 2
def baseEnd_1445079 : Nat := 742020110718656855466709

theorem tailTrace_1445079 : CollatzResearch.WordTrace tailWord_1445079 prefixEnd_1445079 742020110718656855466709 := by
  unfold tailWord_1445079
  simp only [CollatzResearch.WordTrace]
  refine ⟨52706361131733057689570291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35137574087822038459713527 52706361131733057689570291)
  ·
    refine ⟨79059541697599586534355437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52706361131733057689570291 79059541697599586534355437)
    ·
      refine ⟨29647328136599844950383289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79059541697599586534355437 29647328136599844950383289)
      ·
        refine ⟨22235496102449883712787467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29647328136599844950383289 22235496102449883712787467)
        ·
          refine ⟨33353244153674825569181201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22235496102449883712787467 33353244153674825569181201)
          ·
            refine ⟨25014933115256119176885901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33353244153674825569181201 25014933115256119176885901)
            ·
              refine ⟨9380599918221044691332213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25014933115256119176885901 9380599918221044691332213)
              ·
                refine ⟨879431242333222939812395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9380599918221044691332213 879431242333222939812395)
                ·
                  refine ⟨1319146863499834409718593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 879431242333222939812395 1319146863499834409718593)
                  ·
                    refine ⟨989360147624875807288945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1319146863499834409718593 989360147624875807288945)
                    ·
                      refine ⟨742020110718656855466709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 989360147624875807288945 742020110718656855466709)
                      ·
                        rfl

theorem cell23_1445079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 5, 1, 2, 2].length) (baseStart_1445079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1445079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1445079 prefixEnd_1445079 := by exact prefixLift 1445079
  have htrace : WordTrace (prefixWord ++ tailWord_1445079) baseStart_1445079 baseEnd_1445079 := by
    simpa [prefixWord, tailWord_1445079, baseEnd_1445079] using wordTrace_append hprefix tailTrace_1445079
  have hstable : (prefixWord ++ tailWord_1445079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445079).length < 2 ^ (prefixWord ++ tailWord_1445079).sum := by decide
  have hdescent : baseEnd_1445079 < baseStart_1445079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445085 : List Nat := [1, 4, 3, 2, 2, 1, 10]
def baseStart_1445085 : Nat := 118140960795 + 1445085 * 2 ^ 59
def prefixEnd_1445085 : Nat := 4983230072969 + 3 ^ 40 * 1445085 * 2
def baseEnd_1445085 : Nat := 9160780143241775703601

theorem tailTrace_1445085 : CollatzResearch.WordTrace tailWord_1445085 prefixEnd_1445085 9160780143241775703601 := by
  unfold tailWord_1445085
  simp only [CollatzResearch.WordTrace]
  refine ⟨52706579969711320714288709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35137719979807547142859139 52706579969711320714288709)
  ·
    refine ⟨9882483744320872633929133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52706579969711320714288709 9882483744320872633929133)
    ·
      refine ⟨3705931404120327237723425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9882483744320872633929133 3705931404120327237723425)
      ·
        refine ⟨2779448553090245428292569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3705931404120327237723425 2779448553090245428292569)
        ·
          refine ⟨2084586414817684071219427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2779448553090245428292569 2084586414817684071219427)
          ·
            refine ⟨3126879622226526106829141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2084586414817684071219427 3126879622226526106829141)
            ·
              refine ⟨9160780143241775703601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3126879622226526106829141 9160780143241775703601)
              ·
                rfl

theorem cell23_1445085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 10].length) (baseStart_1445085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1445085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1445085 prefixEnd_1445085 := by exact prefixLift 1445085
  have htrace : WordTrace (prefixWord ++ tailWord_1445085) baseStart_1445085 baseEnd_1445085 := by
    simpa [prefixWord, tailWord_1445085, baseEnd_1445085] using wordTrace_append hprefix tailTrace_1445085
  have hstable : (prefixWord ++ tailWord_1445085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445085).length < 2 ^ (prefixWord ++ tailWord_1445085).sum := by decide
  have hdescent : baseEnd_1445085 < baseStart_1445085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445255 : List Nat := [1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 6]
def baseStart_1445255 : Nat := 118140960795 + 1445255 * 2 ^ 59
def prefixEnd_1445255 : Nat := 4983230072969 + 3 ^ 40 * 1445255 * 2
def baseEnd_1445255 : Nat := 742110483313848166865899

theorem tailTrace_1445255 : CollatzResearch.WordTrace tailWord_1445255 prefixEnd_1445255 742110483313848166865899 := by
  unfold tailWord_1445255
  simp only [CollatzResearch.WordTrace]
  refine ⟨52712780379095439747977219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35141853586063626498651479 52712780379095439747977219)
  ·
    refine ⟨79069170568643159621965829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52712780379095439747977219 79069170568643159621965829)
    ·
      refine ⟨14825469481620592429118593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79069170568643159621965829 14825469481620592429118593)
      ·
        refine ⟨11119102111215444321838945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14825469481620592429118593 11119102111215444321838945)
        ·
          refine ⟨8339326583411583241379209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11119102111215444321838945 8339326583411583241379209)
          ·
            refine ⟨6254494937558687431034407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8339326583411583241379209 6254494937558687431034407)
            ·
              refine ⟨9381742406338031146551611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6254494937558687431034407 9381742406338031146551611)
              ·
                refine ⟨14072613609507046719827417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9381742406338031146551611 14072613609507046719827417)
                ·
                  refine ⟨10554460207130285039870563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14072613609507046719827417 10554460207130285039870563)
                  ·
                    refine ⟨15831690310695427559805845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10554460207130285039870563 15831690310695427559805845)
                    ·
                      refine ⟨742110483313848166865899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15831690310695427559805845 742110483313848166865899)
                      ·
                        rfl

theorem cell23_1445255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_1445255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1445255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1445255 prefixEnd_1445255 := by exact prefixLift 1445255
  have htrace : WordTrace (prefixWord ++ tailWord_1445255) baseStart_1445255 baseEnd_1445255 := by
    simpa [prefixWord, tailWord_1445255, baseEnd_1445255] using wordTrace_append hprefix tailTrace_1445255
  have hstable : (prefixWord ++ tailWord_1445255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445255).length < 2 ^ (prefixWord ++ tailWord_1445255).sum := by decide
  have hdescent : baseEnd_1445255 < baseStart_1445255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445269 : List Nat := [1, 3, 2, 1, 1, 2, 4, 4, 1, 4]
def baseStart_1445269 : Nat := 118140960795 + 1445269 * 2 ^ 59
def prefixEnd_1445269 : Nat := 4983230072969 + 3 ^ 40 * 1445269 * 2
def baseEnd_1445269 : Nat := 247372557347670370696945

theorem tailTrace_1445269 : CollatzResearch.WordTrace tailWord_1445269 prefixEnd_1445269 247372557347670370696945 := by
  unfold tailWord_1445269
  simp only [CollatzResearch.WordTrace]
  refine ⟨52713291001044720138986861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35142194000696480092657907 52713291001044720138986861)
  ·
    refine ⟨19767484125391770052120073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52713291001044720138986861 19767484125391770052120073)
    ·
      refine ⟨14825613094043827539090055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19767484125391770052120073 14825613094043827539090055)
      ·
        refine ⟨22238419641065741308635083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14825613094043827539090055 22238419641065741308635083)
        ·
          refine ⟨33357629461598611962952625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22238419641065741308635083 33357629461598611962952625)
          ·
            refine ⟨25018222096198958972214469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33357629461598611962952625 25018222096198958972214469)
            ·
              refine ⟨4690916643037304807290213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25018222096198958972214469 4690916643037304807290213)
              ·
                refine ⟨879546870569494651366915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4690916643037304807290213 879546870569494651366915)
                ·
                  refine ⟨1319320305854241977050373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 879546870569494651366915 1319320305854241977050373)
                  ·
                    refine ⟨247372557347670370696945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1319320305854241977050373 247372557347670370696945)
                    ·
                      rfl

theorem cell23_1445269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 4, 1, 4].length) (baseStart_1445269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1445269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1445269 prefixEnd_1445269 := by exact prefixLift 1445269
  have htrace : WordTrace (prefixWord ++ tailWord_1445269) baseStart_1445269 baseEnd_1445269 := by
    simpa [prefixWord, tailWord_1445269, baseEnd_1445269] using wordTrace_append hprefix tailTrace_1445269
  have hstable : (prefixWord ++ tailWord_1445269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445269).length < 2 ^ (prefixWord ++ tailWord_1445269).sum := by decide
  have hdescent : baseEnd_1445269 < baseStart_1445269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445295 : List Nat := [1, 1, 2, 1, 2, 2, 1, 5, 3, 5]
def baseStart_1445295 : Nat := 118140960795 + 1445295 * 2 ^ 59
def prefixEnd_1445295 : Nat := 4983230072969 + 3 ^ 40 * 1445295 * 2
def baseEnd_1445295 : Nat := 247377007513342670121905

theorem tailTrace_1445295 : CollatzResearch.WordTrace tailWord_1445295 prefixEnd_1445295 247377007513342670121905 := by
  unfold tailWord_1445295
  simp only [CollatzResearch.WordTrace]
  refine ⟨52714239298950526579433339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35142826199300351052955559 52714239298950526579433339)
  ·
    refine ⟨79071358948425789869150009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52714239298950526579433339 79071358948425789869150009)
    ·
      refine ⟨59303519211319342401862507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79071358948425789869150009 59303519211319342401862507)
      ·
        refine ⟨88955278816979013602793761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59303519211319342401862507 88955278816979013602793761)
        ·
          refine ⟨66716459112734260202095321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88955278816979013602793761 66716459112734260202095321)
          ·
            refine ⟨50037344334550695151571491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66716459112734260202095321 50037344334550695151571491)
            ·
              refine ⟨75056016501826042727357237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50037344334550695151571491 75056016501826042727357237)
              ·
                refine ⟨7036501547046191505689741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 75056016501826042727357237 7036501547046191505689741)
                ·
                  refine ⟨2638688080142321814633653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7036501547046191505689741 2638688080142321814633653)
                  ·
                    refine ⟨247377007513342670121905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2638688080142321814633653 247377007513342670121905)
                    ·
                      rfl

theorem cell23_1445295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 3, 5].length) (baseStart_1445295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1445295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1445295 prefixEnd_1445295 := by exact prefixLift 1445295
  have htrace : WordTrace (prefixWord ++ tailWord_1445295) baseStart_1445295 baseEnd_1445295 := by
    simpa [prefixWord, tailWord_1445295, baseEnd_1445295] using wordTrace_append hprefix tailTrace_1445295
  have hstable : (prefixWord ++ tailWord_1445295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445295).length < 2 ^ (prefixWord ++ tailWord_1445295).sum := by decide
  have hdescent : baseEnd_1445295 < baseStart_1445295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445312 : List Nat := [2, 1, 1, 2, 3, 1, 4, 3, 1, 5]
def baseStart_1445312 : Nat := 118140960795 + 1445312 * 2 ^ 59
def prefixEnd_1445312 : Nat := 4983230072969 + 3 ^ 40 * 1445312 * 2
def baseEnd_1445312 : Nat := 247379917237051481284379

theorem tailTrace_1445312 : CollatzResearch.WordTrace tailWord_1445312 prefixEnd_1445312 247379917237051481284379 := by
  unfold tailWord_1445312
  simp only [CollatzResearch.WordTrace]
  refine ⟨26357429669944469241401095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35143239559925958988534793 26357429669944469241401095)
  ·
    refine ⟨39536144504916703862101643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26357429669944469241401095 39536144504916703862101643)
    ·
      refine ⟨59304216757375055793152465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39536144504916703862101643 59304216757375055793152465)
      ·
        refine ⟨44478162568031291844864349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59304216757375055793152465 44478162568031291844864349)
        ·
          refine ⟨16679310963011734441824131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44478162568031291844864349 16679310963011734441824131)
          ·
            refine ⟨25018966444517601662736197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16679310963011734441824131 25018966444517601662736197)
            ·
              refine ⟨4691056208347050311763037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25018966444517601662736197 4691056208347050311763037)
              ·
                refine ⟨1759146078130143866911139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4691056208347050311763037 1759146078130143866911139)
                ·
                  refine ⟨2638719117195215800366709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1759146078130143866911139 2638719117195215800366709)
                  ·
                    refine ⟨247379917237051481284379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2638719117195215800366709 247379917237051481284379)
                    ·
                      rfl

theorem cell23_1445312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 3, 1, 5].length) (baseStart_1445312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1445312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1445312 prefixEnd_1445312 := by exact prefixLift 1445312
  have htrace : WordTrace (prefixWord ++ tailWord_1445312) baseStart_1445312 baseEnd_1445312 := by
    simpa [prefixWord, tailWord_1445312, baseEnd_1445312] using wordTrace_append hprefix tailTrace_1445312
  have hstable : (prefixWord ++ tailWord_1445312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445312).length < 2 ^ (prefixWord ++ tailWord_1445312).sum := by decide
  have hdescent : baseEnd_1445312 < baseStart_1445312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445319 : List Nat := [1, 1, 4, 1, 1, 3, 3, 2, 2, 3, 2]
def baseStart_1445319 : Nat := 118140960795 + 1445319 * 2 ^ 59
def prefixEnd_1445319 : Nat := 4983230072969 + 3 ^ 40 * 1445319 * 2
def baseEnd_1445319 : Nat := 742143346075735916465605

theorem tailTrace_1445319 : CollatzResearch.WordTrace tailWord_1445319 prefixEnd_1445319 742143346075735916465605 := by
  unfold tailWord_1445319
  simp only [CollatzResearch.WordTrace]
  refine ⟨52715114650863578678307011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35143409767242385785538007 52715114650863578678307011)
  ·
    refine ⟨79072671976295368017460517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52715114650863578678307011 79072671976295368017460517)
    ·
      refine ⟨14826125995555381503273847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79072671976295368017460517 14826125995555381503273847)
      ·
        refine ⟨22239188993333072254910771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14826125995555381503273847 22239188993333072254910771)
        ·
          refine ⟨33358783489999608382366157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22239188993333072254910771 33358783489999608382366157)
          ·
            refine ⟨12509543808749853143387309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33358783489999608382366157 12509543808749853143387309)
            ·
              refine ⟨4691078928281194928770241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12509543808749853143387309 4691078928281194928770241)
              ·
                refine ⟨3518309196210896196577681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4691078928281194928770241 3518309196210896196577681)
                ·
                  refine ⟨2638731897158172147433261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3518309196210896196577681 2638731897158172147433261)
                  ·
                    refine ⟨989524461434314555287473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2638731897158172147433261 989524461434314555287473)
                    ·
                      refine ⟨742143346075735916465605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 989524461434314555287473 742143346075735916465605)
                      ·
                        rfl

theorem cell23_1445319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 2, 2, 3, 2].length) (baseStart_1445319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1445319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1445319 prefixEnd_1445319 := by exact prefixLift 1445319
  have htrace : WordTrace (prefixWord ++ tailWord_1445319) baseStart_1445319 baseEnd_1445319 := by
    simpa [prefixWord, tailWord_1445319, baseEnd_1445319] using wordTrace_append hprefix tailTrace_1445319
  have hstable : (prefixWord ++ tailWord_1445319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445319).length < 2 ^ (prefixWord ++ tailWord_1445319).sum := by decide
  have hdescent : baseEnd_1445319 < baseStart_1445319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445326 : List Nat := [4, 1, 1, 1, 2, 1, 2, 6, 1, 1, 3]
def baseStart_1445326 : Nat := 118140960795 + 1445326 * 2 ^ 59
def prefixEnd_1445326 : Nat := 4983230072969 + 3 ^ 40 * 1445326 * 2
def baseEnd_1445326 : Nat := 742146940440317389078073

theorem tailTrace_1445326 : CollatzResearch.WordTrace tailWord_1445326 prefixEnd_1445326 742146940440317389078073 := by
  unfold tailWord_1445326
  simp only [CollatzResearch.WordTrace]
  refine ⟨6589421245229777359226479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35143579974558812582541221 6589421245229777359226479)
  ·
    refine ⟨9884131867844666038839719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6589421245229777359226479 9884131867844666038839719)
    ·
      refine ⟨14826197801766999058259579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9884131867844666038839719 14826197801766999058259579)
      ·
        refine ⟨22239296702650498587389369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14826197801766999058259579 22239296702650498587389369)
        ·
          refine ⟨16679472526987873940542027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22239296702650498587389369 16679472526987873940542027)
          ·
            refine ⟨25019208790481810910813041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16679472526987873940542027 25019208790481810910813041)
            ·
              refine ⟨18764406592861358183109781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25019208790481810910813041 18764406592861358183109781)
              ·
                refine ⟨879581559040376164833271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18764406592861358183109781 879581559040376164833271)
                ·
                  refine ⟨1319372338560564247249907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 879581559040376164833271 1319372338560564247249907)
                  ·
                    refine ⟨1979058507840846370874861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1319372338560564247249907 1979058507840846370874861)
                    ·
                      refine ⟨742146940440317389078073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1979058507840846370874861 742146940440317389078073)
                      ·
                        rfl

theorem cell23_1445326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 6, 1, 1, 3].length) (baseStart_1445326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1445326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1445326 prefixEnd_1445326 := by exact prefixLift 1445326
  have htrace : WordTrace (prefixWord ++ tailWord_1445326) baseStart_1445326 baseEnd_1445326 := by
    simpa [prefixWord, tailWord_1445326, baseEnd_1445326] using wordTrace_append hprefix tailTrace_1445326
  have hstable : (prefixWord ++ tailWord_1445326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445326).length < 2 ^ (prefixWord ++ tailWord_1445326).sum := by decide
  have hdescent : baseEnd_1445326 < baseStart_1445326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445349 : List Nat := [1, 3, 1, 5, 1, 2, 1, 1, 3, 1, 4]
def baseStart_1445349 : Nat := 118140960795 + 1445349 * 2 ^ 59
def prefixEnd_1445349 : Nat := 4983230072969 + 3 ^ 40 * 1445349 * 2
def baseEnd_1445349 : Nat := 742158750495370799090467

theorem tailTrace_1445349 : CollatzResearch.WordTrace tailWord_1445349 prefixEnd_1445349 742158750495370799090467 := by
  unfold tailWord_1445349
  simp only [CollatzResearch.WordTrace]
  refine ⟨52716208840754893801899101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35144139227169929201266067 52716208840754893801899101)
  ·
    refine ⟨19768578315283085175712163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52716208840754893801899101 19768578315283085175712163)
    ·
      refine ⟨29652867472924627763568245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19768578315283085175712163 29652867472924627763568245)
      ·
        refine ⟨2779956325586683852834523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29652867472924627763568245 2779956325586683852834523)
        ·
          refine ⟨4169934488380025779251785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2779956325586683852834523 4169934488380025779251785)
          ·
            refine ⟨3127450866285019334438839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4169934488380025779251785 3127450866285019334438839)
            ·
              refine ⟨4691176299427529001658259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3127450866285019334438839 4691176299427529001658259)
              ·
                refine ⟨7036764449141293502487389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4691176299427529001658259 7036764449141293502487389)
                ·
                  refine ⟨2638786668427985063432771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7036764449141293502487389 2638786668427985063432771)
                  ·
                    refine ⟨3958180002641977595149157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2638786668427985063432771 3958180002641977595149157)
                    ·
                      refine ⟨742158750495370799090467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3958180002641977595149157 742158750495370799090467)
                      ·
                        rfl

theorem cell23_1445349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_1445349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1445349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1445349 prefixEnd_1445349 := by exact prefixLift 1445349
  have htrace : WordTrace (prefixWord ++ tailWord_1445349) baseStart_1445349 baseEnd_1445349 := by
    simpa [prefixWord, tailWord_1445349, baseEnd_1445349] using wordTrace_append hprefix tailTrace_1445349
  have hstable : (prefixWord ++ tailWord_1445349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445349).length < 2 ^ (prefixWord ++ tailWord_1445349).sum := by decide
  have hdescent : baseEnd_1445349 < baseStart_1445349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445375 : List Nat := [1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 6]
def baseStart_1445375 : Nat := 118140960795 + 1445375 * 2 ^ 59
def prefixEnd_1445375 : Nat := 4983230072969 + 3 ^ 40 * 1445375 * 2
def baseEnd_1445375 : Nat := 742172100992387697365347

theorem tailTrace_1445375 : CollatzResearch.WordTrace tailWord_1445375 prefixEnd_1445375 742172100992387697365347 := by
  unfold tailWord_1445375
  simp only [CollatzResearch.WordTrace]
  refine ⟨52717157138660700242345579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35144771425773800161563719 52717157138660700242345579)
  ·
    refine ⟨79075735707991050363518369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52717157138660700242345579 79075735707991050363518369)
    ·
      refine ⟨59306801780993287772638777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79075735707991050363518369 59306801780993287772638777)
      ·
        refine ⟨44480101335744965829479083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59306801780993287772638777 44480101335744965829479083)
        ·
          refine ⟨66720152003617448744218625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44480101335744965829479083 66720152003617448744218625)
          ·
            refine ⟨50040114002713086558163969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66720152003617448744218625 50040114002713086558163969)
            ·
              refine ⟨37530085502034814918622977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50040114002713086558163969 37530085502034814918622977)
              ·
                refine ⟨28147564126526111188967233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37530085502034814918622977 28147564126526111188967233)
                ·
                  refine ⟨21110673094894583391725425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28147564126526111188967233 21110673094894583391725425)
                  ·
                    refine ⟨15833004821170937543794069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21110673094894583391725425 15833004821170937543794069)
                    ·
                      refine ⟨742172100992387697365347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15833004821170937543794069 742172100992387697365347)
                      ·
                        rfl

theorem cell23_1445375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 6].length) (baseStart_1445375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1445375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1445375 prefixEnd_1445375 := by exact prefixLift 1445375
  have htrace : WordTrace (prefixWord ++ tailWord_1445375) baseStart_1445375 baseEnd_1445375 := by
    simpa [prefixWord, tailWord_1445375, baseEnd_1445375] using wordTrace_append hprefix tailTrace_1445375
  have hstable : (prefixWord ++ tailWord_1445375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445375).length < 2 ^ (prefixWord ++ tailWord_1445375).sum := by decide
  have hdescent : baseEnd_1445375 < baseStart_1445375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445377 : List Nat := [1, 2, 4, 1, 5, 1, 2, 2, 1, 1, 3]
def baseStart_1445377 : Nat := 118140960795 + 1445377 * 2 ^ 59
def prefixEnd_1445377 : Nat := 4983230072969 + 3 ^ 40 * 1445377 * 2
def baseEnd_1445377 : Nat := 742173127953696689540339

theorem tailTrace_1445377 : CollatzResearch.WordTrace tailWord_1445377 prefixEnd_1445377 742173127953696689540339 := by
  unfold tailWord_1445377
  simp only [CollatzResearch.WordTrace]
  refine ⟨52717230084653454583918385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35144820056435636389278923 52717230084653454583918385)
  ·
    refine ⟨39537922563490090937938789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52717230084653454583918385 39537922563490090937938789)
    ·
      refine ⟨7413360480654392050863523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39537922563490090937938789 7413360480654392050863523)
      ·
        refine ⟨11120040720981588076295285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7413360480654392050863523 11120040720981588076295285)
        ·
          refine ⟨1042503817592023882152683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11120040720981588076295285 1042503817592023882152683)
          ·
            refine ⟨1563755726388035823229025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1042503817592023882152683 1563755726388035823229025)
            ·
              refine ⟨1172816794791026867421769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1563755726388035823229025 1172816794791026867421769)
              ·
                refine ⟨879612596093270150566327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1172816794791026867421769 879612596093270150566327)
                ·
                  refine ⟨1319418894139905225849491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 879612596093270150566327 1319418894139905225849491)
                  ·
                    refine ⟨1979128341209857838774237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1319418894139905225849491 1979128341209857838774237)
                    ·
                      refine ⟨742173127953696689540339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1979128341209857838774237 742173127953696689540339)
                      ·
                        rfl

theorem cell23_1445377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 2, 2, 1, 1, 3].length) (baseStart_1445377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1445377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1445377 prefixEnd_1445377 := by exact prefixLift 1445377
  have htrace : WordTrace (prefixWord ++ tailWord_1445377) baseStart_1445377 baseEnd_1445377 := by
    simpa [prefixWord, tailWord_1445377, baseEnd_1445377] using wordTrace_append hprefix tailTrace_1445377
  have hstable : (prefixWord ++ tailWord_1445377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445377).length < 2 ^ (prefixWord ++ tailWord_1445377).sum := by decide
  have hdescent : baseEnd_1445377 < baseStart_1445377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445385 : List Nat := [1, 2, 1, 1, 3, 1, 3, 1, 1, 9]
def baseStart_1445385 : Nat := 118140960795 + 1445385 * 2 ^ 59
def prefixEnd_1445385 : Nat := 4983230072969 + 3 ^ 40 * 1445385 * 2
def baseEnd_1445385 : Nat := 247392411932977552746767

theorem tailTrace_1445385 : CollatzResearch.WordTrace tailWord_1445385 prefixEnd_1445385 247392411932977552746767 := by
  unfold tailWord_1445385
  simp only [CollatzResearch.WordTrace]
  refine ⟨52717521868624471950209609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35145014579082981300139739 52717521868624471950209609)
  ·
    refine ⟨39538141401468353962657207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52717521868624471950209609 39538141401468353962657207)
    ·
      refine ⟨59307212102202530943985811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39538141401468353962657207 59307212102202530943985811)
      ·
        refine ⟨88960818153303796415978717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59307212102202530943985811 88960818153303796415978717)
        ·
          refine ⟨33360306807488923655992019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88960818153303796415978717 33360306807488923655992019)
          ·
            refine ⟨50040460211233385483988029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33360306807488923655992019 50040460211233385483988029)
            ·
              refine ⟨18765172579212519556495511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50040460211233385483988029 18765172579212519556495511)
              ·
                refine ⟨28147758868818779334743267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18765172579212519556495511 28147758868818779334743267)
                ·
                  refine ⟨42221638303228169002114901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28147758868818779334743267 42221638303228169002114901)
                  ·
                    refine ⟨247392411932977552746767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 42221638303228169002114901 247392411932977552746767)
                    ·
                      rfl

theorem cell23_1445385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 9].length) (baseStart_1445385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1445385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1445385 prefixEnd_1445385 := by exact prefixLift 1445385
  have htrace : WordTrace (prefixWord ++ tailWord_1445385) baseStart_1445385 baseEnd_1445385 := by
    simpa [prefixWord, tailWord_1445385, baseEnd_1445385] using wordTrace_append hprefix tailTrace_1445385
  have hstable : (prefixWord ++ tailWord_1445385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445385).length < 2 ^ (prefixWord ++ tailWord_1445385).sum := by decide
  have hdescent : baseEnd_1445385 < baseStart_1445385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445432 : List Nat := [2, 1, 2, 1, 4, 2, 1, 2, 2, 6]
def baseStart_1445432 : Nat := 118140960795 + 1445432 * 2 ^ 59
def prefixEnd_1445432 : Nat := 4983230072969 + 3 ^ 40 * 1445432 * 2
def baseEnd_1445432 : Nat := 247400456463231324784195

theorem tailTrace_1445432 : CollatzResearch.WordTrace tailWord_1445432 prefixEnd_1445432 247400456463231324784195 := by
  unfold tailWord_1445432
  simp only [CollatzResearch.WordTrace]
  refine ⟨26359618049727099488585275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35146157399636132651447033 26359618049727099488585275)
  ·
    refine ⟨39539427074590649232877913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26359618049727099488585275 39539427074590649232877913)
    ·
      refine ⟨29654570305942986924658435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39539427074590649232877913 29654570305942986924658435)
      ·
        refine ⟨44481855458914480386987653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29654570305942986924658435 44481855458914480386987653)
        ·
          refine ⟨8340347898546465072560185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44481855458914480386987653 8340347898546465072560185)
          ·
            refine ⟨6255260923909848804420139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8340347898546465072560185 6255260923909848804420139)
            ·
              refine ⟨9382891385864773206630209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6255260923909848804420139 9382891385864773206630209)
              ·
                refine ⟨7037168539398579904972657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9382891385864773206630209 7037168539398579904972657)
                ·
                  refine ⟨5277876404548934928729493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7037168539398579904972657 5277876404548934928729493)
                  ·
                    refine ⟨247400456463231324784195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5277876404548934928729493 247400456463231324784195)
                    ·
                      rfl

theorem cell23_1445432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 2, 6].length) (baseStart_1445432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1445432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1445432 prefixEnd_1445432 := by exact prefixLift 1445432
  have htrace : WordTrace (prefixWord ++ tailWord_1445432) baseStart_1445432 baseEnd_1445432 := by
    simpa [prefixWord, tailWord_1445432, baseEnd_1445432] using wordTrace_append hprefix tailTrace_1445432
  have hstable : (prefixWord ++ tailWord_1445432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445432).length < 2 ^ (prefixWord ++ tailWord_1445432).sum := by decide
  have hdescent : baseEnd_1445432 < baseStart_1445432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445433 : List Nat := [1, 2, 1, 5, 1, 4, 1, 2, 2, 1, 3]
def baseStart_1445433 : Nat := 118140960795 + 1445433 * 2 ^ 59
def prefixEnd_1445433 : Nat := 4983230072969 + 3 ^ 40 * 1445433 * 2
def baseEnd_1445433 : Nat := 742201882870348470440081

theorem tailTrace_1445433 : CollatzResearch.WordTrace tailWord_1445433 prefixEnd_1445433 742201882870348470440081 := by
  unfold tailWord_1445433
  simp only [CollatzResearch.WordTrace]
  refine ⟨52719272572450576147956953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35146181714967050765304635 52719272572450576147956953)
  ·
    refine ⟨39539454429337932110967715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52719272572450576147956953 39539454429337932110967715)
    ·
      refine ⟨59309181644006898166451573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39539454429337932110967715 59309181644006898166451573)
      ·
        refine ⟨5560235779125646703104835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59309181644006898166451573 5560235779125646703104835)
        ·
          refine ⟨8340353668688470054657253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5560235779125646703104835 8340353668688470054657253)
          ·
            refine ⟨1563816312879088135248235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8340353668688470054657253 1563816312879088135248235)
            ·
              refine ⟨2345724469318632202872353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1563816312879088135248235 2345724469318632202872353)
              ·
                refine ⟨1759293351988974152154265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2345724469318632202872353 1759293351988974152154265)
                ·
                  refine ⟨1319470013991730614115699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1759293351988974152154265 1319470013991730614115699)
                  ·
                    refine ⟨1979205020987595921173549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1319470013991730614115699 1979205020987595921173549)
                    ·
                      refine ⟨742201882870348470440081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1979205020987595921173549 742201882870348470440081)
                      ·
                        rfl

theorem cell23_1445433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_1445433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1445433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1445433 prefixEnd_1445433 := by exact prefixLift 1445433
  have htrace : WordTrace (prefixWord ++ tailWord_1445433) baseStart_1445433 baseEnd_1445433 := by
    simpa [prefixWord, tailWord_1445433, baseEnd_1445433] using wordTrace_append hprefix tailTrace_1445433
  have hstable : (prefixWord ++ tailWord_1445433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445433).length < 2 ^ (prefixWord ++ tailWord_1445433).sum := by decide
  have hdescent : baseEnd_1445433 < baseStart_1445433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445499 : List Nat := [1, 1, 1, 1, 1, 4, 4, 1, 2, 5, 2]
def baseStart_1445499 : Nat := 118140960795 + 1445499 * 2 ^ 59
def prefixEnd_1445499 : Nat := 4983230072969 + 3 ^ 40 * 1445499 * 2
def baseEnd_1445499 : Nat := 742235772593545212214777

theorem tailTrace_1445499 : CollatzResearch.WordTrace tailWord_1445499 prefixEnd_1445499 742235772593545212214777 := by
  unfold tailWord_1445499
  simp only [CollatzResearch.WordTrace]
  refine ⟨52721679790211469419859551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35147786526807646279906367 52721679790211469419859551)
  ·
    refine ⟨79082519685317204129789327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52721679790211469419859551 79082519685317204129789327)
    ·
      refine ⟨118623779527975806194683991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79082519685317204129789327 118623779527975806194683991)
      ·
        refine ⟨177935669291963709292025987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118623779527975806194683991 177935669291963709292025987)
        ·
          refine ⟨266903503937945563938038981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177935669291963709292025987 266903503937945563938038981)
          ·
            refine ⟨50044406988364793238382309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 266903503937945563938038981 50044406988364793238382309)
            ·
              refine ⟨9383326310318398732196683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50044406988364793238382309 9383326310318398732196683)
              ·
                refine ⟨14074989465477598098295025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9383326310318398732196683 14074989465477598098295025)
                ·
                  refine ⟨10556242099108198573721269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14074989465477598098295025 10556242099108198573721269)
                  ·
                    refine ⟨989647696791393616286369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10556242099108198573721269 989647696791393616286369)
                    ·
                      refine ⟨742235772593545212214777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 989647696791393616286369 742235772593545212214777)
                      ·
                        rfl

theorem cell23_1445499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 5, 2].length) (baseStart_1445499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1445499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1445499 prefixEnd_1445499 := by exact prefixLift 1445499
  have htrace : WordTrace (prefixWord ++ tailWord_1445499) baseStart_1445499 baseEnd_1445499 := by
    simpa [prefixWord, tailWord_1445499, baseEnd_1445499] using wordTrace_append hprefix tailTrace_1445499
  have hstable : (prefixWord ++ tailWord_1445499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445499).length < 2 ^ (prefixWord ++ tailWord_1445499).sum := by decide
  have hdescent : baseEnd_1445499 < baseStart_1445499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445529 : List Nat := [1, 2, 1, 2, 1, 2, 2, 1, 3, 6, 2]
def baseStart_1445529 : Nat := 118140960795 + 1445529 * 2 ^ 59
def prefixEnd_1445529 : Nat := 4983230072969 + 3 ^ 40 * 1445529 * 2
def baseEnd_1445529 : Nat := 742251177013180094839639

theorem tailTrace_1445529 : CollatzResearch.WordTrace tailWord_1445529 prefixEnd_1445529 742251177013180094839639 := by
  unfold tailWord_1445529
  simp only [CollatzResearch.WordTrace]
  refine ⟨52722773980102784543451641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35148515986735189695634427 52722773980102784543451641)
  ·
    refine ⟨39542080485077088407588731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52722773980102784543451641 39542080485077088407588731)
    ·
      refine ⟨59313120727615632611383097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39542080485077088407588731 59313120727615632611383097)
      ·
        refine ⟨44484840545711724458537323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59313120727615632611383097 44484840545711724458537323)
        ·
          refine ⟨66727260818567586687805985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44484840545711724458537323 66727260818567586687805985)
          ·
            refine ⟨50045445613925690015854489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66727260818567586687805985 50045445613925690015854489)
            ·
              refine ⟨37534084210444267511890867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50045445613925690015854489 37534084210444267511890867)
              ·
                refine ⟨56301126315666401267836301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37534084210444267511890867 56301126315666401267836301)
                ·
                  refine ⟨21112922368374900475438613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56301126315666401267836301 21112922368374900475438613)
                  ·
                    refine ⟨989668236017573459786185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21112922368374900475438613 989668236017573459786185)
                    ·
                      refine ⟨742251177013180094839639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 989668236017573459786185 742251177013180094839639)
                      ·
                        rfl

theorem cell23_1445529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 6, 2].length) (baseStart_1445529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1445529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1445529 prefixEnd_1445529 := by exact prefixLift 1445529
  have htrace : WordTrace (prefixWord ++ tailWord_1445529) baseStart_1445529 baseEnd_1445529 := by
    simpa [prefixWord, tailWord_1445529, baseEnd_1445529] using wordTrace_append hprefix tailTrace_1445529
  have hstable : (prefixWord ++ tailWord_1445529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445529).length < 2 ^ (prefixWord ++ tailWord_1445529).sum := by decide
  have hdescent : baseEnd_1445529 < baseStart_1445529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445549 : List Nat := [1, 5, 2, 1, 1, 1, 1, 1, 2, 3, 5]
def baseStart_1445549 : Nat := 118140960795 + 1445549 * 2 ^ 59
def prefixEnd_1445549 : Nat := 4983230072969 + 3 ^ 40 * 1445549 * 2
def baseEnd_1445549 : Nat := 742261446626270016589547

theorem tailTrace_1445549 : CollatzResearch.WordTrace tailWord_1445549 prefixEnd_1445549 742261446626270016589547 := by
  unfold tailWord_1445549
  simp only [CollatzResearch.WordTrace]
  refine ⟨52723503440030327959179701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35149002293353551972786467 52723503440030327959179701)
  ·
    refine ⟨4942828447502843246173097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52723503440030327959179701 4942828447502843246173097)
    ·
      refine ⟨3707121335627132434629823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4942828447502843246173097 3707121335627132434629823)
      ·
        refine ⟨5560682003440698651944735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3707121335627132434629823 5560682003440698651944735)
        ·
          refine ⟨8341023005161047977917103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5560682003440698651944735 8341023005161047977917103)
          ·
            refine ⟨12511534507741571966875655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8341023005161047977917103 12511534507741571966875655)
            ·
              refine ⟨18767301761612357950313483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12511534507741571966875655 18767301761612357950313483)
              ·
                refine ⟨28150952642418536925470225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18767301761612357950313483 28150952642418536925470225)
                ·
                  refine ⟨21113214481813902694102669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28150952642418536925470225 21113214481813902694102669)
                  ·
                    refine ⟨7917455430680213510288501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21113214481813902694102669 7917455430680213510288501)
                    ·
                      refine ⟨742261446626270016589547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7917455430680213510288501 742261446626270016589547)
                      ·
                        rfl

theorem cell23_1445549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_1445549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1445549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1445549 prefixEnd_1445549 := by exact prefixLift 1445549
  have htrace : WordTrace (prefixWord ++ tailWord_1445549) baseStart_1445549 baseEnd_1445549 := by
    simpa [prefixWord, tailWord_1445549, baseEnd_1445549] using wordTrace_append hprefix tailTrace_1445549
  have hstable : (prefixWord ++ tailWord_1445549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445549).length < 2 ^ (prefixWord ++ tailWord_1445549).sum := by decide
  have hdescent : baseEnd_1445549 < baseStart_1445549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445552 : List Nat := [2, 1, 1, 1, 2, 1, 4, 3, 8]
def baseStart_1445552 : Nat := 118140960795 + 1445552 * 2 ^ 59
def prefixEnd_1445552 : Nat := 4983230072969 + 3 ^ 40 * 1445552 * 2
def baseEnd_1445552 : Nat := 82473665229803722761337

theorem tailTrace_1445552 : CollatzResearch.WordTrace tailWord_1445552 prefixEnd_1445552 82473665229803722761337 := by
  unfold tailWord_1445552
  simp only [CollatzResearch.WordTrace]
  refine ⟨26361806429509729735769455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35149075239346306314359273 26361806429509729735769455)
  ·
    refine ⟨39542709644264594603654183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26361806429509729735769455 39542709644264594603654183)
    ·
      refine ⟨59314064466396891905481275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39542709644264594603654183 59314064466396891905481275)
      ·
        refine ⟨88971096699595337858221913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59314064466396891905481275 88971096699595337858221913)
        ·
          refine ⟨66728322524696503393666435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88971096699595337858221913 66728322524696503393666435)
          ·
            refine ⟨100092483787044755090499653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66728322524696503393666435 100092483787044755090499653)
            ·
              refine ⟨18767340710070891579468685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 100092483787044755090499653 18767340710070891579468685)
              ·
                refine ⟨7037752766276584342300757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18767340710070891579468685 7037752766276584342300757)
                ·
                  refine ⟨82473665229803722761337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7037752766276584342300757 82473665229803722761337)
                  ·
                    rfl

theorem cell23_1445552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 8].length) (baseStart_1445552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1445552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1445552 prefixEnd_1445552 := by exact prefixLift 1445552
  have htrace : WordTrace (prefixWord ++ tailWord_1445552) baseStart_1445552 baseEnd_1445552 := by
    simpa [prefixWord, tailWord_1445552, baseEnd_1445552] using wordTrace_append hprefix tailTrace_1445552
  have hstable : (prefixWord ++ tailWord_1445552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445552).length < 2 ^ (prefixWord ++ tailWord_1445552).sum := by decide
  have hdescent : baseEnd_1445552 < baseStart_1445552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445580 : List Nat := [2, 2, 1, 5, 3, 1, 1, 1, 2, 1, 4]
def baseStart_1445580 : Nat := 118140960795 + 1445580 * 2 ^ 59
def prefixEnd_1445580 : Nat := 4983230072969 + 3 ^ 40 * 1445580 * 2
def baseEnd_1445580 : Nat := 742277364526559395301905

theorem tailTrace_1445580 : CollatzResearch.WordTrace tailWord_1445580 prefixEnd_1445580 742277364526559395301905 := by
  unfold tailWord_1445580
  simp only [CollatzResearch.WordTrace]
  refine ⟨26362317051459010126779097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35149756068612013502372129 26362317051459010126779097)
  ·
    refine ⟨19771737788594257595084323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26362317051459010126779097 19771737788594257595084323)
    ·
      refine ⟨29657606682891386392626485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19771737788594257595084323 29657606682891386392626485)
      ·
        refine ⟨2780400626521067474308733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29657606682891386392626485 2780400626521067474308733)
        ·
          refine ⟨1042650234945400302865775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2780400626521067474308733 1042650234945400302865775)
          ·
            refine ⟨1563975352418100454298663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1042650234945400302865775 1563975352418100454298663)
            ·
              refine ⟨2345963028627150681447995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1563975352418100454298663 2345963028627150681447995)
              ·
                refine ⟨3518944542940726022171993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2345963028627150681447995 3518944542940726022171993)
                ·
                  refine ⟨2639208407205544516628995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3518944542940726022171993 2639208407205544516628995)
                  ·
                    refine ⟨3958812610808316774943493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2639208407205544516628995 3958812610808316774943493)
                    ·
                      refine ⟨742277364526559395301905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3958812610808316774943493 742277364526559395301905)
                      ·
                        rfl

theorem cell23_1445580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_1445580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1445580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1445580 prefixEnd_1445580 := by exact prefixLift 1445580
  have htrace : WordTrace (prefixWord ++ tailWord_1445580) baseStart_1445580 baseEnd_1445580 := by
    simpa [prefixWord, tailWord_1445580, baseEnd_1445580] using wordTrace_append hprefix tailTrace_1445580
  have hstable : (prefixWord ++ tailWord_1445580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445580).length < 2 ^ (prefixWord ++ tailWord_1445580).sum := by decide
  have hdescent : baseEnd_1445580 < baseStart_1445580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445603 : List Nat := [1, 1, 1, 7, 2, 2, 1, 2, 6]
def baseStart_1445603 : Nat := 118140960795 + 1445603 * 2 ^ 59
def prefixEnd_1445603 : Nat := 4983230072969 + 3 ^ 40 * 1445603 * 2
def baseEnd_1445603 : Nat := 82476574953512533923811

theorem tailTrace_1445603 : CollatzResearch.WordTrace tailWord_1445603 prefixEnd_1445603 82476574953512533923811 := by
  unfold tailWord_1445603
  simp only [CollatzResearch.WordTrace]
  refine ⟨52725472981834695181645463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35150315321223130121096975 52725472981834695181645463)
  ·
    refine ⟨79088209472752042772468195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52725472981834695181645463 79088209472752042772468195)
    ·
      refine ⟨118632314209128064158702293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79088209472752042772468195 118632314209128064158702293)
      ·
        refine ⟨2780444864276439003719585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 118632314209128064158702293 2780444864276439003719585)
        ·
          refine ⟨2085333648207329252789689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2780444864276439003719585 2085333648207329252789689)
          ·
            refine ⟨1564000236155496939592267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2085333648207329252789689 1564000236155496939592267)
            ·
              refine ⟨2346000354233245409388401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1564000236155496939592267 2346000354233245409388401)
              ·
                refine ⟨1759500265674934057041301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2346000354233245409388401 1759500265674934057041301)
                ·
                  refine ⟨82476574953512533923811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1759500265674934057041301 82476574953512533923811)
                  ·
                    rfl

theorem cell23_1445603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 2, 6].length) (baseStart_1445603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1445603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1445603 prefixEnd_1445603 := by exact prefixLift 1445603
  have htrace : WordTrace (prefixWord ++ tailWord_1445603) baseStart_1445603 baseEnd_1445603 := by
    simpa [prefixWord, tailWord_1445603, baseEnd_1445603] using wordTrace_append hprefix tailTrace_1445603
  have hstable : (prefixWord ++ tailWord_1445603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445603).length < 2 ^ (prefixWord ++ tailWord_1445603).sum := by decide
  have hdescent : baseEnd_1445603 < baseStart_1445603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445613 : List Nat := [1, 5, 1, 2, 1, 2, 1, 3, 3, 1, 3]
def baseStart_1445613 : Nat := 118140960795 + 1445613 * 2 ^ 59
def prefixEnd_1445613 : Nat := 4983230072969 + 3 ^ 40 * 1445613 * 2
def baseEnd_1445613 : Nat := 742294309388157766189253

theorem tailTrace_1445613 : CollatzResearch.WordTrace tailWord_1445613 prefixEnd_1445613 742294309388157766189253 := by
  unfold tailWord_1445613
  simp only [CollatzResearch.WordTrace]
  refine ⟨52725837711798466889509493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35150558474532311259672995 52725837711798466889509493)
  ·
    refine ⟨4943047285481106270891515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52725837711798466889509493 4943047285481106270891515)
    ·
      refine ⟨7414570928221659406337273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4943047285481106270891515 7414570928221659406337273)
      ·
        refine ⟨5560928196166244554752955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7414570928221659406337273 5560928196166244554752955)
        ·
          refine ⟨8341392294249366832129433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5560928196166244554752955 8341392294249366832129433)
          ·
            refine ⟨6256044220687025124097075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8341392294249366832129433 6256044220687025124097075)
            ·
              refine ⟨9384066331030537686145613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6256044220687025124097075 9384066331030537686145613)
              ·
                refine ⟨3519024874136451632304605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9384066331030537686145613 3519024874136451632304605)
                ·
                  refine ⟨1319634327801169362114227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3519024874136451632304605 1319634327801169362114227)
                  ·
                    refine ⟨1979451491701754043171341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1319634327801169362114227 1979451491701754043171341)
                    ·
                      refine ⟨742294309388157766189253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1979451491701754043171341 742294309388157766189253)
                      ·
                        rfl

theorem cell23_1445613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_1445613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1445613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1445613 prefixEnd_1445613 := by exact prefixLift 1445613
  have htrace : WordTrace (prefixWord ++ tailWord_1445613) baseStart_1445613 baseEnd_1445613 := by
    simpa [prefixWord, tailWord_1445613, baseEnd_1445613] using wordTrace_append hprefix tailTrace_1445613
  have hstable : (prefixWord ++ tailWord_1445613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445613).length < 2 ^ (prefixWord ++ tailWord_1445613).sum := by decide
  have hdescent : baseEnd_1445613 < baseStart_1445613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445619 : List Nat := [1, 1, 1, 2, 2, 3, 2, 1, 5, 1, 4]
def baseStart_1445619 : Nat := 118140960795 + 1445619 * 2 ^ 59
def prefixEnd_1445619 : Nat := 4983230072969 + 3 ^ 40 * 1445619 * 2
def baseEnd_1445619 : Nat := 742297390272084742714225

theorem tailTrace_1445619 : CollatzResearch.WordTrace tailWord_1445619 prefixEnd_1445619 742297390272084742714225 := by
  unfold tailWord_1445619
  simp only [CollatzResearch.WordTrace]
  refine ⟨52726056549776729914227911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35150704366517819942818607 52726056549776729914227911)
  ·
    refine ⟨79089084824665094871341867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52726056549776729914227911 79089084824665094871341867)
    ·
      refine ⟨118633627236997642307012801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79089084824665094871341867 118633627236997642307012801)
      ·
        refine ⟨88975220427748231730259601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118633627236997642307012801 88975220427748231730259601)
        ·
          refine ⟨66731415320811173797694701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88975220427748231730259601 66731415320811173797694701)
          ·
            refine ⟨25024280745304190174135513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66731415320811173797694701 25024280745304190174135513)
            ·
              refine ⟨18768210558978142630601635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25024280745304190174135513 18768210558978142630601635)
              ·
                refine ⟨28152315838467213945902453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18768210558978142630601635 28152315838467213945902453)
                ·
                  refine ⟨2639279609856301307428355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28152315838467213945902453 2639279609856301307428355)
                  ·
                    refine ⟨3958919414784451961142533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2639279609856301307428355 3958919414784451961142533)
                    ·
                      refine ⟨742297390272084742714225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3958919414784451961142533 742297390272084742714225)
                      ·
                        rfl

theorem cell23_1445619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 5, 1, 4].length) (baseStart_1445619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1445619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1445619 prefixEnd_1445619 := by exact prefixLift 1445619
  have htrace : WordTrace (prefixWord ++ tailWord_1445619) baseStart_1445619 baseEnd_1445619 := by
    simpa [prefixWord, tailWord_1445619, baseEnd_1445619] using wordTrace_append hprefix tailTrace_1445619
  have hstable : (prefixWord ++ tailWord_1445619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445619).length < 2 ^ (prefixWord ++ tailWord_1445619).sum := by decide
  have hdescent : baseEnd_1445619 < baseStart_1445619 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445629 : List Nat := [1, 4, 1, 1, 1, 1, 2, 5, 1, 6]
def baseStart_1445629 : Nat := 118140960795 + 1445629 * 2 ^ 59
def prefixEnd_1445629 : Nat := 4983230072969 + 3 ^ 40 * 1445629 * 2
def baseEnd_1445629 : Nat := 247434175026209901196393

theorem tailTrace_1445629 : CollatzResearch.WordTrace tailWord_1445629 prefixEnd_1445629 247434175026209901196393 := by
  unfold tailWord_1445629
  simp only [CollatzResearch.WordTrace]
  refine ⟨52726421279740501622091941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35150947519827001081394627 52726421279740501622091941)
  ·
    refine ⟨9886203989951344054142239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52726421279740501622091941 9886203989951344054142239)
    ·
      refine ⟨14829305984927016081213359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9886203989951344054142239 14829305984927016081213359)
      ·
        refine ⟨22243958977390524121820039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14829305984927016081213359 22243958977390524121820039)
        ·
          refine ⟨33365938466085786182730059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22243958977390524121820039 33365938466085786182730059)
          ·
            refine ⟨50048907699128679274095089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33365938466085786182730059 50048907699128679274095089)
            ·
              refine ⟨37536680774346509455571317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50048907699128679274095089 37536680774346509455571317)
              ·
                refine ⟨3519063822594985261459811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37536680774346509455571317 3519063822594985261459811)
                ·
                  refine ⟨5278595733892477892189717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3519063822594985261459811 5278595733892477892189717)
                  ·
                    refine ⟨247434175026209901196393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5278595733892477892189717 247434175026209901196393)
                    ·
                      rfl

theorem cell23_1445629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 5, 1, 6].length) (baseStart_1445629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1445629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1445629 prefixEnd_1445629 := by exact prefixLift 1445629
  have htrace : WordTrace (prefixWord ++ tailWord_1445629) baseStart_1445629 baseEnd_1445629 := by
    simpa [prefixWord, tailWord_1445629, baseEnd_1445629] using wordTrace_append hprefix tailTrace_1445629
  have hstable : (prefixWord ++ tailWord_1445629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445629).length < 2 ^ (prefixWord ++ tailWord_1445629).sum := by decide
  have hdescent : baseEnd_1445629 < baseStart_1445629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445646 : List Nat := [4, 1, 1, 2, 1, 1, 3, 2, 4, 4]
def baseStart_1445646 : Nat := 118140960795 + 1445646 * 2 ^ 59
def prefixEnd_1445646 : Nat := 4983230072969 + 3 ^ 40 * 1445646 * 2
def baseEnd_1445646 : Nat := 247437084749918712358867

theorem tailTrace_1445646 : CollatzResearch.WordTrace tailWord_1445646 prefixEnd_1445646 247437084749918712358867 := by
  unfold tailWord_1445646
  simp only [CollatzResearch.WordTrace]
  refine ⟨6590880165084864190682599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35151360880452609016973861 6590880165084864190682599)
  ·
    refine ⟨9886320247627296286023899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6590880165084864190682599 9886320247627296286023899)
    ·
      refine ⟨14829480371440944429035849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9886320247627296286023899 14829480371440944429035849)
      ·
        refine ⟨11122110278580708321776887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14829480371440944429035849 11122110278580708321776887)
        ·
          refine ⟨16683165417871062482665331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11122110278580708321776887 16683165417871062482665331)
          ·
            refine ⟨25024748126806593723997997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16683165417871062482665331 25024748126806593723997997)
            ·
              refine ⟨9384280547552472646499249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25024748126806593723997997 9384280547552472646499249)
              ·
                refine ⟨7038210410664354484874437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9384280547552472646499249 7038210410664354484874437)
                ·
                  refine ⟨1319664451999566465913957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7038210410664354484874437 1319664451999566465913957)
                  ·
                    refine ⟨247437084749918712358867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1319664451999566465913957 247437084749918712358867)
                    ·
                      rfl

theorem cell23_1445646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 4, 4].length) (baseStart_1445646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1445646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1445646 prefixEnd_1445646 := by exact prefixLift 1445646
  have htrace : WordTrace (prefixWord ++ tailWord_1445646) baseStart_1445646 baseEnd_1445646 := by
    simpa [prefixWord, tailWord_1445646, baseEnd_1445646] using wordTrace_append hprefix tailTrace_1445646
  have hstable : (prefixWord ++ tailWord_1445646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445646).length < 2 ^ (prefixWord ++ tailWord_1445646).sum := by decide
  have hdescent : baseEnd_1445646 < baseStart_1445646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445649 : List Nat := [1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 4]
def baseStart_1445649 : Nat := 118140960795 + 1445649 * 2 ^ 59
def prefixEnd_1445649 : Nat := 4983230072969 + 3 ^ 40 * 1445649 * 2
def baseEnd_1445649 : Nat := 742312794691719625339087

theorem tailTrace_1445649 : CollatzResearch.WordTrace tailWord_1445649 prefixEnd_1445649 742312794691719625339087 := by
  unfold tailWord_1445649
  simp only [CollatzResearch.WordTrace]
  refine ⟨52727150739668045037820001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35151433826445363358546667 52727150739668045037820001)
  ·
    refine ⟨39545363054751033778365001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52727150739668045037820001 39545363054751033778365001)
    ·
      refine ⟨29659022291063275333773751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39545363054751033778365001 29659022291063275333773751)
      ·
        refine ⟨44488533436594913000660627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29659022291063275333773751 44488533436594913000660627)
        ·
          refine ⟨66732800154892369500990941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44488533436594913000660627 66732800154892369500990941)
          ·
            refine ⟨25024800058084638562871603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66732800154892369500990941 25024800058084638562871603)
            ·
              refine ⟨37537200087126957844307405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25024800058084638562871603 37537200087126957844307405)
              ·
                refine ⟨14076450032672609191615277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37537200087126957844307405 14076450032672609191615277)
                ·
                  refine ⟨5278668762252228446855729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14076450032672609191615277 5278668762252228446855729)
                  ·
                    refine ⟨3959001571689171335141797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5278668762252228446855729 3959001571689171335141797)
                    ·
                      refine ⟨742312794691719625339087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3959001571689171335141797 742312794691719625339087)
                      ·
                        rfl

theorem cell23_1445649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 4].length) (baseStart_1445649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1445649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1445649 prefixEnd_1445649 := by exact prefixLift 1445649
  have htrace : WordTrace (prefixWord ++ tailWord_1445649) baseStart_1445649 baseEnd_1445649 := by
    simpa [prefixWord, tailWord_1445649, baseEnd_1445649] using wordTrace_append hprefix tailTrace_1445649
  have hstable : (prefixWord ++ tailWord_1445649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445649).length < 2 ^ (prefixWord ++ tailWord_1445649).sum := by decide
  have hdescent : baseEnd_1445649 < baseStart_1445649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445690 : List Nat := [3, 1, 1, 1, 5, 3, 1, 2, 1, 2, 3]
def baseStart_1445690 : Nat := 118140960795 + 1445690 * 2 ^ 59
def prefixEnd_1445690 : Nat := 4983230072969 + 3 ^ 40 * 1445690 * 2
def baseEnd_1445690 : Nat := 742333847398553964926399

theorem tailTrace_1445690 : CollatzResearch.WordTrace tailWord_1445690 prefixEnd_1445690 742333847398553964926399 := by
  unfold tailWord_1445690
  simp only [CollatzResearch.WordTrace]
  refine ⟨13182161533129877260015631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35152430755013006026708349 13182161533129877260015631)
  ·
    refine ⟨19773242299694815890023447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13182161533129877260015631 19773242299694815890023447)
    ·
      refine ⟨29659863449542223835035171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19773242299694815890023447 29659863449542223835035171)
      ·
        refine ⟨44489795174313335752552757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29659863449542223835035171 44489795174313335752552757)
        ·
          refine ⟨4170918297591875226801821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44489795174313335752552757 4170918297591875226801821)
          ·
            refine ⟨1564094361596953210050683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4170918297591875226801821 1564094361596953210050683)
            ·
              refine ⟨2346141542395429815076025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1564094361596953210050683 2346141542395429815076025)
              ·
                refine ⟨1759606156796572361307019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2346141542395429815076025 1759606156796572361307019)
                ·
                  refine ⟨2639409235194858541960529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1759606156796572361307019 2639409235194858541960529)
                  ·
                    refine ⟨1979556926396143906470397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2639409235194858541960529 1979556926396143906470397)
                    ·
                      refine ⟨742333847398553964926399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1979556926396143906470397 742333847398553964926399)
                      ·
                        rfl

theorem cell23_1445690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 2, 1, 2, 3].length) (baseStart_1445690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1445690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1445690 prefixEnd_1445690 := by exact prefixLift 1445690
  have htrace : WordTrace (prefixWord ++ tailWord_1445690) baseStart_1445690 baseEnd_1445690 := by
    simpa [prefixWord, tailWord_1445690, baseEnd_1445690] using wordTrace_append hprefix tailTrace_1445690
  have hstable : (prefixWord ++ tailWord_1445690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445690).length < 2 ^ (prefixWord ++ tailWord_1445690).sum := by decide
  have hdescent : baseEnd_1445690 < baseStart_1445690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445730 : List Nat := [3, 3, 2, 1, 2, 1, 1, 2, 3, 3, 2]
def baseStart_1445730 : Nat := 118140960795 + 1445730 * 2 ^ 59
def prefixEnd_1445730 : Nat := 4983230072969 + 3 ^ 40 * 1445730 * 2
def baseEnd_1445730 : Nat := 742354386624733808426215

theorem tailTrace_1445730 : CollatzResearch.WordTrace tailWord_1445730 prefixEnd_1445730 742354386624733808426215 := by
  unfold tailWord_1445730
  simp only [CollatzResearch.WordTrace]
  refine ⟨13182526263093648967879661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35153403368249730581012429 13182526263093648967879661)
  ·
    refine ⟨4943447348660118362954873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13182526263093648967879661 4943447348660118362954873)
    ·
      refine ⟨3707585511495088772216155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4943447348660118362954873 3707585511495088772216155)
      ·
        refine ⟨5561378267242633158324233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3707585511495088772216155 5561378267242633158324233)
        ·
          refine ⟨4171033700431974868743175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5561378267242633158324233 4171033700431974868743175)
          ·
            refine ⟨6256550550647962303114763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4171033700431974868743175 6256550550647962303114763)
            ·
              refine ⟨9384825825971943454672145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6256550550647962303114763 9384825825971943454672145)
              ·
                refine ⟨7038619369478957591004109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9384825825971943454672145 7038619369478957591004109)
                ·
                  refine ⟨2639482263554609096626541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7038619369478957591004109 2639482263554609096626541)
                  ·
                    refine ⟨989805848832978411234953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2639482263554609096626541 989805848832978411234953)
                    ·
                      refine ⟨742354386624733808426215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 989805848832978411234953 742354386624733808426215)
                      ·
                        rfl

theorem cell23_1445730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 3, 3, 2].length) (baseStart_1445730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1445730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1445730 prefixEnd_1445730 := by exact prefixLift 1445730
  have htrace : WordTrace (prefixWord ++ tailWord_1445730) baseStart_1445730 baseEnd_1445730 := by
    simpa [prefixWord, tailWord_1445730, baseEnd_1445730] using wordTrace_append hprefix tailTrace_1445730
  have hstable : (prefixWord ++ tailWord_1445730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445730).length < 2 ^ (prefixWord ++ tailWord_1445730).sum := by decide
  have hdescent : baseEnd_1445730 < baseStart_1445730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445736 : List Nat := [2, 1, 4, 2, 1, 1, 3, 1, 2, 6]
def baseStart_1445736 : Nat := 118140960795 + 1445736 * 2 ^ 59
def prefixEnd_1445736 : Nat := 4983230072969 + 3 ^ 40 * 1445736 * 2
def baseEnd_1445736 : Nat := 247452489169553594983729

theorem tailTrace_1445736 : CollatzResearch.WordTrace tailWord_1445736 prefixEnd_1445736 247452489169553594983729 := by
  unfold tailWord_1445736
  simp only [CollatzResearch.WordTrace]
  refine ⟨26365161945176429448118531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35153549260235239264158041 26365161945176429448118531)
  ·
    refine ⟨39547742917764644172177797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26365161945176429448118531 39547742917764644172177797)
    ·
      refine ⟨7415201797080870782283337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39547742917764644172177797 7415201797080870782283337)
      ·
        refine ⟨5561401347810653086712503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7415201797080870782283337 5561401347810653086712503)
        ·
          refine ⟨8342102021715979630068755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5561401347810653086712503 8342102021715979630068755)
          ·
            refine ⟨12513153032573969445103133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8342102021715979630068755 12513153032573969445103133)
            ·
              refine ⟨4692432387215238541913675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12513153032573969445103133 4692432387215238541913675)
              ·
                refine ⟨7038648580822857812870513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4692432387215238541913675 7038648580822857812870513)
                ·
                  refine ⟨5278986435617143359652885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7038648580822857812870513 5278986435617143359652885)
                  ·
                    refine ⟨247452489169553594983729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5278986435617143359652885 247452489169553594983729)
                    ·
                      rfl

theorem cell23_1445736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_1445736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1445736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1445736 prefixEnd_1445736 := by exact prefixLift 1445736
  have htrace : WordTrace (prefixWord ++ tailWord_1445736) baseStart_1445736 baseEnd_1445736 := by
    simpa [prefixWord, tailWord_1445736, baseEnd_1445736] using wordTrace_append hprefix tailTrace_1445736
  have hstable : (prefixWord ++ tailWord_1445736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445736).length < 2 ^ (prefixWord ++ tailWord_1445736).sum := by decide
  have hdescent : baseEnd_1445736 < baseStart_1445736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445743 : List Nat := [1, 1, 2, 1, 3, 1, 1, 1, 8, 2, 2]
def baseStart_1445743 : Nat := 118140960795 + 1445743 * 2 ^ 59
def prefixEnd_1445743 : Nat := 4983230072969 + 3 ^ 40 * 1445743 * 2
def baseEnd_1445743 : Nat := 742361061873242257563655

theorem tailTrace_1445743 : CollatzResearch.WordTrace tailWord_1445743 prefixEnd_1445743 742361061873242257563655 := by
  unfold tailWord_1445743
  simp only [CollatzResearch.WordTrace]
  refine ⟨52730579201327499091741883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35153719467551666061161255 52730579201327499091741883)
  ·
    refine ⟨79095868801991248637612825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52730579201327499091741883 79095868801991248637612825)
    ·
      refine ⟨59321901601493436478209619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79095868801991248637612825 59321901601493436478209619)
      ·
        refine ⟨88982852402240154717314429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59321901601493436478209619 88982852402240154717314429)
        ·
          refine ⟨33368569650840058018992911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88982852402240154717314429 33368569650840058018992911)
          ·
            refine ⟨50052854476260087028489367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33368569650840058018992911 50052854476260087028489367)
            ·
              refine ⟨75079281714390130542734051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50052854476260087028489367 75079281714390130542734051)
              ·
                refine ⟨112618922571585195814101077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75079281714390130542734051 112618922571585195814101077)
                ·
                  refine ⟨1319752998885764013446497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 112618922571585195814101077 1319752998885764013446497)
                  ·
                    refine ⟨989814749164323010084873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1319752998885764013446497 989814749164323010084873)
                    ·
                      refine ⟨742361061873242257563655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 989814749164323010084873 742361061873242257563655)
                      ·
                        rfl

theorem cell23_1445743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 8, 2, 2].length) (baseStart_1445743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1445743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1445743 prefixEnd_1445743 := by exact prefixLift 1445743
  have htrace : WordTrace (prefixWord ++ tailWord_1445743) baseStart_1445743 baseEnd_1445743 := by
    simpa [prefixWord, tailWord_1445743, baseEnd_1445743] using wordTrace_append hprefix tailTrace_1445743
  have hstable : (prefixWord ++ tailWord_1445743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445743).length < 2 ^ (prefixWord ++ tailWord_1445743).sum := by decide
  have hdescent : baseEnd_1445743 < baseStart_1445743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445746 : List Nat := [3, 2, 1, 2, 1, 1, 1, 1, 4, 4, 3]
def baseStart_1445746 : Nat := 118140960795 + 1445746 * 2 ^ 59
def prefixEnd_1445746 : Nat := 4983230072969 + 3 ^ 40 * 1445746 * 2
def baseEnd_1445746 : Nat := 742362602315205745826141

theorem tailTrace_1445746 : CollatzResearch.WordTrace tailWord_1445746 prefixEnd_1445746 742362602315205745826141 := by
  unfold tailWord_1445746
  simp only [CollatzResearch.WordTrace]
  refine ⟨13182672155079157651025273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35153792413544420402734061 13182672155079157651025273)
  ·
    refine ⟨9887004116309368238268955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13182672155079157651025273 9887004116309368238268955)
    ·
      refine ⟨14830506174464052357403433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9887004116309368238268955 14830506174464052357403433)
      ·
        refine ⟨11122879630848039268052575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14830506174464052357403433 11122879630848039268052575)
        ·
          refine ⟨16684319446272058902078863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11122879630848039268052575 16684319446272058902078863)
          ·
            refine ⟨25026479169408088353118295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16684319446272058902078863 25026479169408088353118295)
            ·
              refine ⟨37539718754112132529677443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25026479169408088353118295 37539718754112132529677443)
              ·
                refine ⟨56309578131168198794516165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37539718754112132529677443 56309578131168198794516165)
                ·
                  refine ⟨10558045899594037273971781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56309578131168198794516165 10558045899594037273971781)
                  ·
                    refine ⟨1979633606173881988869709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10558045899594037273971781 1979633606173881988869709)
                    ·
                      refine ⟨742362602315205745826141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1979633606173881988869709 742362602315205745826141)
                      ·
                        rfl

theorem cell23_1445746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 4, 4, 3].length) (baseStart_1445746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1445746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1445746 prefixEnd_1445746 := by exact prefixLift 1445746
  have htrace : WordTrace (prefixWord ++ tailWord_1445746) baseStart_1445746 baseEnd_1445746 := by
    simpa [prefixWord, tailWord_1445746, baseEnd_1445746] using wordTrace_append hprefix tailTrace_1445746
  have hstable : (prefixWord ++ tailWord_1445746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445746).length < 2 ^ (prefixWord ++ tailWord_1445746).sum := by decide
  have hdescent : baseEnd_1445746 < baseStart_1445746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445759 : List Nat := [1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 7]
def baseStart_1445759 : Nat := 118140960795 + 1445759 * 2 ^ 59
def prefixEnd_1445759 : Nat := 4983230072969 + 3 ^ 40 * 1445759 * 2
def baseEnd_1445759 : Nat := 742369277563714194963581

theorem tailTrace_1445759 : CollatzResearch.WordTrace tailWord_1445759 prefixEnd_1445759 742369277563714194963581 := by
  unfold tailWord_1445759
  simp only [CollatzResearch.WordTrace]
  refine ⟨52731162769269533824324331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35154108512846355882882887 52731162769269533824324331)
  ·
    refine ⟨79096744153904300736486497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52731162769269533824324331 79096744153904300736486497)
    ·
      refine ⟨59322558115428225552364873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79096744153904300736486497 59322558115428225552364873)
      ·
        refine ⟨44491918586571169164273655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59322558115428225552364873 44491918586571169164273655)
        ·
          refine ⟨66737877879856753746410483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44491918586571169164273655 66737877879856753746410483)
          ·
            refine ⟨100106816819785130619615725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66737877879856753746410483 100106816819785130619615725)
            ·
              refine ⟨37540056307419423982355897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100106816819785130619615725 37540056307419423982355897)
              ·
                refine ⟨28155042230564567986766923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37540056307419423982355897 28155042230564567986766923)
                ·
                  refine ⟨42232563345846851980150385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28155042230564567986766923 42232563345846851980150385)
                  ·
                    refine ⟨31674422509385138985112789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42232563345846851980150385 31674422509385138985112789)
                    ·
                      refine ⟨742369277563714194963581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 31674422509385138985112789 742369277563714194963581)
                      ·
                        rfl

theorem cell23_1445759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 7].length) (baseStart_1445759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1445759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1445759 prefixEnd_1445759 := by exact prefixLift 1445759
  have htrace : WordTrace (prefixWord ++ tailWord_1445759) baseStart_1445759 baseEnd_1445759 := by
    simpa [prefixWord, tailWord_1445759, baseEnd_1445759] using wordTrace_append hprefix tailTrace_1445759
  have hstable : (prefixWord ++ tailWord_1445759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445759).length < 2 ^ (prefixWord ++ tailWord_1445759).sum := by decide
  have hdescent : baseEnd_1445759 < baseStart_1445759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445776 : List Nat := [2, 1, 1, 1, 1, 1, 2, 6, 2, 3, 3]
def baseStart_1445776 : Nat := 118140960795 + 1445776 * 2 ^ 59
def prefixEnd_1445776 : Nat := 4983230072969 + 3 ^ 40 * 1445776 * 2
def baseEnd_1445776 : Nat := 742378006734840628451003

theorem tailTrace_1445776 : CollatzResearch.WordTrace tailWord_1445776 prefixEnd_1445776 742378006734840628451003 := by
  unfold tailWord_1445776
  simp only [CollatzResearch.WordTrace]
  refine ⟨26365891405103972863846591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35154521873471963818462121 26365891405103972863846591)
  ·
    refine ⟨39548837107655959295769887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26365891405103972863846591 39548837107655959295769887)
    ·
      refine ⟨59323255661483938943654831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39548837107655959295769887 59323255661483938943654831)
      ·
        refine ⟨88984883492225908415482247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59323255661483938943654831 88984883492225908415482247)
        ·
          refine ⟨133477325238338862623223371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88984883492225908415482247 133477325238338862623223371)
          ·
            refine ⟨200215987857508293934835057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133477325238338862623223371 200215987857508293934835057)
            ·
              refine ⟨150161990893131220451126293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200215987857508293934835057 150161990893131220451126293)
              ·
                refine ⟨7038843323115525958646545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 150161990893131220451126293 7038843323115525958646545)
                ·
                  refine ⟨5279132492336644468984909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7038843323115525958646545 5279132492336644468984909)
                  ·
                    refine ⟨1979674684626241675869341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5279132492336644468984909 1979674684626241675869341)
                    ·
                      refine ⟨742378006734840628451003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1979674684626241675869341 742378006734840628451003)
                      ·
                        rfl

theorem cell23_1445776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 2, 3, 3].length) (baseStart_1445776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1445776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1445776 prefixEnd_1445776 := by exact prefixLift 1445776
  have htrace : WordTrace (prefixWord ++ tailWord_1445776) baseStart_1445776 baseEnd_1445776 := by
    simpa [prefixWord, tailWord_1445776, baseEnd_1445776] using wordTrace_append hprefix tailTrace_1445776
  have hstable : (prefixWord ++ tailWord_1445776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445776).length < 2 ^ (prefixWord ++ tailWord_1445776).sum := by decide
  have hdescent : baseEnd_1445776 < baseStart_1445776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445783 : List Nat := [1, 1, 3, 3, 1, 3, 2, 4, 5]
def baseStart_1445783 : Nat := 118140960795 + 1445783 * 2 ^ 59
def prefixEnd_1445783 : Nat := 4983230072969 + 3 ^ 40 * 1445783 * 2
def baseEnd_1445783 : Nat := 82486844566602455673719

theorem tailTrace_1445783 : CollatzResearch.WordTrace tailWord_1445783 prefixEnd_1445783 82486844566602455673719 := by
  unfold tailWord_1445783
  simp only [CollatzResearch.WordTrace]
  refine ⟨52732038121182585923198003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35154692080788390615465335 52732038121182585923198003)
  ·
    refine ⟨79098057181773878884797005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52732038121182585923198003 79098057181773878884797005)
    ·
      refine ⟨29661771443165204581798877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79098057181773878884797005 29661771443165204581798877)
      ·
        refine ⟨11123164291186951718174579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29661771443165204581798877 11123164291186951718174579)
        ·
          refine ⟨16684746436780427577261869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11123164291186951718174579 16684746436780427577261869)
          ·
            refine ⟨6256779913792660341473201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16684746436780427577261869 6256779913792660341473201)
            ·
              refine ⟨4692584935344495256104901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6256779913792660341473201 4692584935344495256104901)
              ·
                refine ⟨879859675377092860519669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4692584935344495256104901 879859675377092860519669)
                ·
                  refine ⟨82486844566602455673719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 879859675377092860519669 82486844566602455673719)
                  ·
                    rfl

theorem cell23_1445783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 4, 5].length) (baseStart_1445783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1445783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1445783 prefixEnd_1445783 := by exact prefixLift 1445783
  have htrace : WordTrace (prefixWord ++ tailWord_1445783) baseStart_1445783 baseEnd_1445783 := by
    simpa [prefixWord, tailWord_1445783, baseEnd_1445783] using wordTrace_append hprefix tailTrace_1445783
  have hstable : (prefixWord ++ tailWord_1445783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445783).length < 2 ^ (prefixWord ++ tailWord_1445783).sum := by decide
  have hdescent : baseEnd_1445783 < baseStart_1445783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445794 : List Nat := [3, 3, 1, 2, 4, 1, 1, 1, 1, 4, 2]
def baseStart_1445794 : Nat := 118140960795 + 1445794 * 2 ^ 59
def prefixEnd_1445794 : Nat := 4983230072969 + 3 ^ 40 * 1445794 * 2
def baseEnd_1445794 : Nat := 742387249386621558025921

theorem tailTrace_1445794 : CollatzResearch.WordTrace tailWord_1445794 prefixEnd_1445794 742387249386621558025921 := by
  unfold tailWord_1445794
  simp only [CollatzResearch.WordTrace]
  refine ⟨13183109831035683700462109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35154959549428489867898957 13183109831035683700462109)
  ·
    refine ⟨4943666186638381387673291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13183109831035683700462109 4943666186638381387673291)
    ·
      refine ⟨7415499279957572081509937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4943666186638381387673291 7415499279957572081509937)
      ·
        refine ⟨5561624459968179061132453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7415499279957572081509937 5561624459968179061132453)
        ·
          refine ⟨1042804586244033573962335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5561624459968179061132453 1042804586244033573962335)
          ·
            refine ⟨1564206879366050360943503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1042804586244033573962335 1564206879366050360943503)
            ·
              refine ⟨2346310319049075541415255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1564206879366050360943503 2346310319049075541415255)
              ·
                refine ⟨3519465478573613312122883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2346310319049075541415255 3519465478573613312122883)
                ·
                  refine ⟨5279198217860419968184325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3519465478573613312122883 5279198217860419968184325)
                  ·
                    refine ⟨989849665848828744034561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5279198217860419968184325 989849665848828744034561)
                    ·
                      refine ⟨742387249386621558025921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 989849665848828744034561 742387249386621558025921)
                      ·
                        rfl

theorem cell23_1445794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 1, 1, 4, 2].length) (baseStart_1445794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1445794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1445794 prefixEnd_1445794 := by exact prefixLift 1445794
  have htrace : WordTrace (prefixWord ++ tailWord_1445794) baseStart_1445794 baseEnd_1445794 := by
    simpa [prefixWord, tailWord_1445794, baseEnd_1445794] using wordTrace_append hprefix tailTrace_1445794
  have hstable : (prefixWord ++ tailWord_1445794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445794).length < 2 ^ (prefixWord ++ tailWord_1445794).sum := by decide
  have hdescent : baseEnd_1445794 < baseStart_1445794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445796 : List Nat := [2, 3, 1, 2, 1, 3, 1, 2, 1, 7]
def baseStart_1445796 : Nat := 118140960795 + 1445796 * 2 ^ 59
def prefixEnd_1445796 : Nat := 4983230072969 + 3 ^ 40 * 1445796 * 2
def baseEnd_1445796 : Nat := 247462758782643516733637

theorem tailTrace_1445796 : CollatzResearch.WordTrace tailWord_1445796 prefixEnd_1445796 247462758782643516733637 := by
  unfold tailWord_1445796
  simp only [CollatzResearch.WordTrace]
  refine ⟨26366256135067744571710621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35155008180090326095614161 26366256135067744571710621)
  ·
    refine ⟨9887346050650404214391483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26366256135067744571710621 9887346050650404214391483)
    ·
      refine ⟨14831019075975606321587225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9887346050650404214391483 14831019075975606321587225)
      ·
        refine ⟨11123264306981704741190419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14831019075975606321587225 11123264306981704741190419)
        ·
          refine ⟨16684896460472557111785629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11123264306981704741190419 16684896460472557111785629)
          ·
            refine ⟨6256836172677208916919611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16684896460472557111785629 6256836172677208916919611)
            ·
              refine ⟨9385254259015813375379417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6256836172677208916919611 9385254259015813375379417)
              ·
                refine ⟨7038940694261860031534563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9385254259015813375379417 7038940694261860031534563)
                ·
                  refine ⟨10558411041392790047301845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7038940694261860031534563 10558411041392790047301845)
                  ·
                    refine ⟨247462758782643516733637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10558411041392790047301845 247462758782643516733637)
                    ·
                      rfl

theorem cell23_1445796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 1, 7].length) (baseStart_1445796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1445796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1445796 prefixEnd_1445796 := by exact prefixLift 1445796
  have htrace : WordTrace (prefixWord ++ tailWord_1445796) baseStart_1445796 baseEnd_1445796 := by
    simpa [prefixWord, tailWord_1445796, baseEnd_1445796] using wordTrace_append hprefix tailTrace_1445796
  have hstable : (prefixWord ++ tailWord_1445796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445796).length < 2 ^ (prefixWord ++ tailWord_1445796).sum := by decide
  have hdescent : baseEnd_1445796 < baseStart_1445796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445816 : List Nat := [2, 1, 2, 1, 2, 3, 1, 3, 1, 3, 4]
def baseStart_1445816 : Nat := 118140960795 + 1445816 * 2 ^ 59
def prefixEnd_1445816 : Nat := 4983230072969 + 3 ^ 40 * 1445816 * 2
def baseEnd_1445816 : Nat := 742398545961020471950819

theorem tailTrace_1445816 : CollatzResearch.WordTrace tailWord_1445816 prefixEnd_1445816 742398545961020471950819 := by
  unfold tailWord_1445816
  simp only [CollatzResearch.WordTrace]
  refine ⟨26366620865031516279574651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35155494486708688372766201 26366620865031516279574651)
  ·
    refine ⟨39549931297547274419361977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26366620865031516279574651 39549931297547274419361977)
    ·
      refine ⟨29662448473160455814521483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39549931297547274419361977 29662448473160455814521483)
      ·
        refine ⟨44493672709740683721782225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29662448473160455814521483 44493672709740683721782225)
        ·
          refine ⟨33370254532305512791336669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44493672709740683721782225 33370254532305512791336669)
          ·
            refine ⟨12513845449614567296751251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33370254532305512791336669 12513845449614567296751251)
            ·
              refine ⟨18770768174421850945126877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12513845449614567296751251 18770768174421850945126877)
              ·
                refine ⟨7039038065408194104422579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18770768174421850945126877 7039038065408194104422579)
                ·
                  refine ⟨10558557098112291156633869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7039038065408194104422579 10558557098112291156633869)
                  ·
                    refine ⟨3959458911792109183737701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10558557098112291156633869 3959458911792109183737701)
                    ·
                      refine ⟨742398545961020471950819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3959458911792109183737701 742398545961020471950819)
                      ·
                        rfl

theorem cell23_1445816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 1, 3, 4].length) (baseStart_1445816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1445816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1445816 prefixEnd_1445816 := by exact prefixLift 1445816
  have htrace : WordTrace (prefixWord ++ tailWord_1445816) baseStart_1445816 baseEnd_1445816 := by
    simpa [prefixWord, tailWord_1445816, baseEnd_1445816] using wordTrace_append hprefix tailTrace_1445816
  have hstable : (prefixWord ++ tailWord_1445816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445816).length < 2 ^ (prefixWord ++ tailWord_1445816).sum := by decide
  have hdescent : baseEnd_1445816 < baseStart_1445816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445870 : List Nat := [4, 1, 2, 1, 3, 1, 1, 3, 2, 2, 3]
def baseStart_1445870 : Nat := 118140960795 + 1445870 * 2 ^ 59
def prefixEnd_1445870 : Nat := 4983230072969 + 3 ^ 40 * 1445870 * 2
def baseEnd_1445870 : Nat := 742426273916363260675571

theorem tailTrace_1445870 : CollatzResearch.WordTrace tailWord_1445870 prefixEnd_1445870 742426273916363260675571 := by
  unfold tailWord_1445870
  simp only [CollatzResearch.WordTrace]
  refine ⟨6591901408983424972701883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35156807514578266521076709 6591901408983424972701883)
  ·
    refine ⟨9887852113475137459052825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6591901408983424972701883 9887852113475137459052825)
    ·
      refine ⟨7415889085106353094289619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9887852113475137459052825 7415889085106353094289619)
      ·
        refine ⟨11123833627659529641434429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7415889085106353094289619 11123833627659529641434429)
        ·
          refine ⟨4171437610372323615537911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11123833627659529641434429 4171437610372323615537911)
          ·
            refine ⟨6257156415558485423306867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4171437610372323615537911 6257156415558485423306867)
            ·
              refine ⟨9385734623337728134960301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6257156415558485423306867 9385734623337728134960301)
              ·
                refine ⟨3519650483751648050610113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9385734623337728134960301 3519650483751648050610113)
                ·
                  refine ⟨2639737862813736037957585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3519650483751648050610113 2639737862813736037957585)
                  ·
                    refine ⟨1979803397110302028468189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2639737862813736037957585 1979803397110302028468189)
                    ·
                      refine ⟨742426273916363260675571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1979803397110302028468189 742426273916363260675571)
                      ·
                        rfl

theorem cell23_1445870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 3, 2, 2, 3].length) (baseStart_1445870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1445870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1445870 prefixEnd_1445870 := by exact prefixLift 1445870
  have htrace : WordTrace (prefixWord ++ tailWord_1445870) baseStart_1445870 baseEnd_1445870 := by
    simpa [prefixWord, tailWord_1445870, baseEnd_1445870] using wordTrace_append hprefix tailTrace_1445870
  have hstable : (prefixWord ++ tailWord_1445870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445870).length < 2 ^ (prefixWord ++ tailWord_1445870).sum := by decide
  have hdescent : baseEnd_1445870 < baseStart_1445870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445900 : List Nat := [2, 2, 1, 2, 3, 1, 2, 3, 3, 1, 3]
def baseStart_1445900 : Nat := 118140960795 + 1445900 * 2 ^ 59
def prefixEnd_1445900 : Nat := 4983230072969 + 3 ^ 40 * 1445900 * 2
def baseEnd_1445900 : Nat := 742441678335998143300433

theorem tailTrace_1445900 : CollatzResearch.WordTrace tailWord_1445900 prefixEnd_1445900 742441678335998143300433 := by
  unfold tailWord_1445900
  simp only [CollatzResearch.WordTrace]
  refine ⟨26368152730879357452603577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35157536974505809936804769 26368152730879357452603577)
  ·
    refine ⟨19776114548159518089452683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26368152730879357452603577 19776114548159518089452683)
    ·
      refine ⟨29664171822239277134179025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19776114548159518089452683 29664171822239277134179025)
      ·
        refine ⟨22248128866679457850634269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29664171822239277134179025 22248128866679457850634269)
        ·
          refine ⟨8343048325004796693987851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22248128866679457850634269 8343048325004796693987851)
          ·
            refine ⟨12514572487507195040981777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8343048325004796693987851 12514572487507195040981777)
            ·
              refine ⟨9385929365630396280736333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12514572487507195040981777 9385929365630396280736333)
              ·
                refine ⟨3519723512111398605276125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9385929365630396280736333 3519723512111398605276125)
                ·
                  refine ⟨1319896317041774476978547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3519723512111398605276125 1319896317041774476978547)
                  ·
                    refine ⟨1979844475562661715467821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1319896317041774476978547 1979844475562661715467821)
                    ·
                      refine ⟨742441678335998143300433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1979844475562661715467821 742441678335998143300433)
                      ·
                        rfl

theorem cell23_1445900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 3, 3, 1, 3].length) (baseStart_1445900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1445900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1445900 prefixEnd_1445900 := by exact prefixLift 1445900
  have htrace : WordTrace (prefixWord ++ tailWord_1445900) baseStart_1445900 baseEnd_1445900 := by
    simpa [prefixWord, tailWord_1445900, baseEnd_1445900] using wordTrace_append hprefix tailTrace_1445900
  have hstable : (prefixWord ++ tailWord_1445900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445900).length < 2 ^ (prefixWord ++ tailWord_1445900).sum := by decide
  have hdescent : baseEnd_1445900 < baseStart_1445900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445901 : List Nat := [1, 7, 1, 2, 1, 1, 1, 1, 2, 4, 2]
def baseStart_1445901 : Nat := 118140960795 + 1445901 * 2 ^ 59
def prefixEnd_1445901 : Nat := 4983230072969 + 3 ^ 40 * 1445901 * 2
def baseEnd_1445901 : Nat := 742442191816652639387929

theorem tailTrace_1445901 : CollatzResearch.WordTrace tailWord_1445901 prefixEnd_1445901 742442191816652639387929 := by
  unfold tailWord_1445901
  simp only [CollatzResearch.WordTrace]
  refine ⟨52736341934755092075993557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35157561289836728050662371 52736341934755092075993557)
  ·
    refine ⟨1236008014095822470531099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 52736341934755092075993557 1236008014095822470531099)
    ·
      refine ⟨1854012021143733705796649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1236008014095822470531099 1854012021143733705796649)
      ·
        refine ⟨1390509015857800279347487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1854012021143733705796649 1390509015857800279347487)
        ·
          refine ⟨2085763523786700419021231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1390509015857800279347487 2085763523786700419021231)
          ·
            refine ⟨3128645285680050628531847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2085763523786700419021231 3128645285680050628531847)
            ·
              refine ⟨4692967928520075942797771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3128645285680050628531847 4692967928520075942797771)
              ·
                refine ⟨7039451892780113914196657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4692967928520075942797771 7039451892780113914196657)
                ·
                  refine ⟨5279588919585085435647493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7039451892780113914196657 5279588919585085435647493)
                  ·
                    refine ⟨989922922422203519183905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5279588919585085435647493 989922922422203519183905)
                    ·
                      refine ⟨742442191816652639387929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 989922922422203519183905 742442191816652639387929)
                      ·
                        rfl

theorem cell23_1445901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_1445901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1445901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1445901 prefixEnd_1445901 := by exact prefixLift 1445901
  have htrace : WordTrace (prefixWord ++ tailWord_1445901) baseStart_1445901 baseEnd_1445901 := by
    simpa [prefixWord, tailWord_1445901, baseEnd_1445901] using wordTrace_append hprefix tailTrace_1445901
  have hstable : (prefixWord ++ tailWord_1445901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445901).length < 2 ^ (prefixWord ++ tailWord_1445901).sum := by decide
  have hdescent : baseEnd_1445901 < baseStart_1445901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445917 : List Nat := [1, 4, 2, 2, 2, 2, 1, 2, 3, 1, 3]
def baseStart_1445917 : Nat := 118140960795 + 1445917 * 2 ^ 59
def prefixEnd_1445917 : Nat := 4983230072969 + 3 ^ 40 * 1445917 * 2
def baseEnd_1445917 : Nat := 742450407507124576787855

theorem tailTrace_1445917 : CollatzResearch.WordTrace tailWord_1445917 prefixEnd_1445917 742450407507124576787855 := by
  unfold tailWord_1445917
  simp only [CollatzResearch.WordTrace]
  refine ⟨52736925502697126808576005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35157950335131417872384003 52736925502697126808576005)
  ·
    refine ⟨9888173531755711276608001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52736925502697126808576005 9888173531755711276608001)
    ·
      refine ⟨7416130148816783457456001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9888173531755711276608001 7416130148816783457456001)
      ·
        refine ⟨5562097611612587593092001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7416130148816783457456001 5562097611612587593092001)
        ·
          refine ⟨4171573208709440694819001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5562097611612587593092001 4171573208709440694819001)
          ·
            refine ⟨3128679906532080521114251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4171573208709440694819001 3128679906532080521114251)
            ·
              refine ⟨4693019859798120781671377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3128679906532080521114251 4693019859798120781671377)
              ·
                refine ⟨3519764894848590586253533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4693019859798120781671377 3519764894848590586253533)
                ·
                  refine ⟨1319911835568221469845075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3519764894848590586253533 1319911835568221469845075)
                  ·
                    refine ⟨1979867753352332204767613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1319911835568221469845075 1979867753352332204767613)
                    ·
                      refine ⟨742450407507124576787855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1979867753352332204767613 742450407507124576787855)
                      ·
                        rfl

theorem cell23_1445917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_1445917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1445917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1445917 prefixEnd_1445917 := by exact prefixLift 1445917
  have htrace : WordTrace (prefixWord ++ tailWord_1445917) baseStart_1445917 baseEnd_1445917 := by
    simpa [prefixWord, tailWord_1445917, baseEnd_1445917] using wordTrace_append hprefix tailTrace_1445917
  have hstable : (prefixWord ++ tailWord_1445917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445917).length < 2 ^ (prefixWord ++ tailWord_1445917).sum := by decide
  have hdescent : baseEnd_1445917 < baseStart_1445917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445923 : List Nat := [1, 1, 1, 4, 3, 1, 1, 3, 3, 1, 4]
def baseStart_1445923 : Nat := 118140960795 + 1445923 * 2 ^ 59
def prefixEnd_1445923 : Nat := 4983230072969 + 3 ^ 40 * 1445923 * 2
def baseEnd_1445923 : Nat := 742453488391051553312827

theorem tailTrace_1445923 : CollatzResearch.WordTrace tailWord_1445923 prefixEnd_1445923 742453488391051553312827 := by
  unfold tailWord_1445923
  simp only [CollatzResearch.WordTrace]
  refine ⟨52737144340675389833294423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35158096227116926555529615 52737144340675389833294423)
  ·
    refine ⟨79105716511013084749941635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52737144340675389833294423 79105716511013084749941635)
    ·
      refine ⟨118658574766519627124912453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79105716511013084749941635 118658574766519627124912453)
      ·
        refine ⟨22248482768722430085921085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118658574766519627124912453 22248482768722430085921085)
        ·
          refine ⟨8343181038270911282220407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22248482768722430085921085 8343181038270911282220407)
          ·
            refine ⟨12514771557406366923330611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8343181038270911282220407 12514771557406366923330611)
            ·
              refine ⟨18772157336109550384995917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12514771557406366923330611 18772157336109550384995917)
              ·
                refine ⟨7039559001041081394373469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18772157336109550384995917 7039559001041081394373469)
                ·
                  refine ⟨2639834625390405522890051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7039559001041081394373469 2639834625390405522890051)
                  ·
                    refine ⟨3959751938085608284335077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2639834625390405522890051 3959751938085608284335077)
                    ·
                      refine ⟨742453488391051553312827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3959751938085608284335077 742453488391051553312827)
                      ·
                        rfl

theorem cell23_1445923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 3, 1, 4].length) (baseStart_1445923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1445923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1445923 prefixEnd_1445923 := by exact prefixLift 1445923
  have htrace : WordTrace (prefixWord ++ tailWord_1445923) baseStart_1445923 baseEnd_1445923 := by
    simpa [prefixWord, tailWord_1445923, baseEnd_1445923] using wordTrace_append hprefix tailTrace_1445923
  have hstable : (prefixWord ++ tailWord_1445923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445923).length < 2 ^ (prefixWord ++ tailWord_1445923).sum := by decide
  have hdescent : baseEnd_1445923 < baseStart_1445923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445934 : List Nat := [4, 1, 3, 1, 1, 2, 1, 5, 1, 1, 3]
def baseStart_1445934 : Nat := 118140960795 + 1445934 * 2 ^ 59
def prefixEnd_1445934 : Nat := 4983230072969 + 3 ^ 40 * 1445934 * 2
def baseEnd_1445934 : Nat := 742459136678251010275277

theorem tailTrace_1445934 : CollatzResearch.WordTrace tailWord_1445934 prefixEnd_1445934 742459136678251010275277 := by
  unfold tailWord_1445934
  simp only [CollatzResearch.WordTrace]
  refine ⟨6592193192954442338993107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35158363695757025807963237 6592193192954442338993107)
  ·
    refine ⟨9888289789431663508489661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6592193192954442338993107 9888289789431663508489661)
    ·
      refine ⟨3708108671036873815683623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9888289789431663508489661 3708108671036873815683623)
      ·
        refine ⟨5562163006555310723525435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3708108671036873815683623 5562163006555310723525435)
        ·
          refine ⟨8343244509832966085288153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5562163006555310723525435 8343244509832966085288153)
          ·
            refine ⟨6257433382374724563966115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8343244509832966085288153 6257433382374724563966115)
            ·
              refine ⟨9386150073562086845949173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6257433382374724563966115 9386150073562086845949173)
              ·
                refine ⟨879951569396445641807735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9386150073562086845949173 879951569396445641807735)
                ·
                  refine ⟨1319927354094668462711603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 879951569396445641807735 1319927354094668462711603)
                  ·
                    refine ⟨1979891031142002694067405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1319927354094668462711603 1979891031142002694067405)
                    ·
                      refine ⟨742459136678251010275277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1979891031142002694067405 742459136678251010275277)
                      ·
                        rfl

theorem cell23_1445934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 5, 1, 1, 3].length) (baseStart_1445934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1445934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1445934 prefixEnd_1445934 := by exact prefixLift 1445934
  have htrace : WordTrace (prefixWord ++ tailWord_1445934) baseStart_1445934 baseEnd_1445934 := by
    simpa [prefixWord, tailWord_1445934, baseEnd_1445934] using wordTrace_append hprefix tailTrace_1445934
  have hstable : (prefixWord ++ tailWord_1445934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445934).length < 2 ^ (prefixWord ++ tailWord_1445934).sum := by decide
  have hdescent : baseEnd_1445934 < baseStart_1445934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445937 : List Nat := [1, 2, 2, 3, 1, 5, 2, 1, 1, 5]
def baseStart_1445937 : Nat := 118140960795 + 1445937 * 2 ^ 59
def prefixEnd_1445937 : Nat := 4983230072969 + 3 ^ 40 * 1445937 * 2
def baseEnd_1445937 : Nat := 247486892373404832845921

theorem tailTrace_1445937 : CollatzResearch.WordTrace tailWord_1445937 prefixEnd_1445937 247486892373404832845921 := by
  unfold tailWord_1445937
  simp only [CollatzResearch.WordTrace]
  refine ⟨52737654962624670224304065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35158436641749780149536043 52737654962624670224304065)
  ·
    refine ⟨39553241221968502668228049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52737654962624670224304065 39553241221968502668228049)
    ·
      refine ⟨29664930916476377001171037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39553241221968502668228049 29664930916476377001171037)
      ·
        refine ⟨11124349093678641375439139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29664930916476377001171037 11124349093678641375439139)
        ·
          refine ⟨16686523640517962063158709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11124349093678641375439139 16686523640517962063158709)
          ·
            refine ⟨1564361591298558943421129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16686523640517962063158709 1564361591298558943421129)
            ·
              refine ⟨1173271193473919207565847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1564361591298558943421129 1173271193473919207565847)
              ·
                refine ⟨1759906790210878811348771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1173271193473919207565847 1759906790210878811348771)
                ·
                  refine ⟨2639860185316318217023157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1759906790210878811348771 2639860185316318217023157)
                  ·
                    refine ⟨247486892373404832845921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2639860185316318217023157 247486892373404832845921)
                    ·
                      rfl

theorem cell23_1445937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 2, 1, 1, 5].length) (baseStart_1445937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1445937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1445937 prefixEnd_1445937 := by exact prefixLift 1445937
  have htrace : WordTrace (prefixWord ++ tailWord_1445937) baseStart_1445937 baseEnd_1445937 := by
    simpa [prefixWord, tailWord_1445937, baseEnd_1445937] using wordTrace_append hprefix tailTrace_1445937
  have hstable : (prefixWord ++ tailWord_1445937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445937).length < 2 ^ (prefixWord ++ tailWord_1445937).sum := by decide
  have hdescent : baseEnd_1445937 < baseStart_1445937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445970 : List Nat := [3, 2, 2, 1, 4, 1, 1, 1, 1, 1, 6]
def baseStart_1445970 : Nat := 118140960795 + 1445970 * 2 ^ 59
def prefixEnd_1445970 : Nat := 4983230072969 + 3 ^ 40 * 1445970 * 2
def baseEnd_1445970 : Nat := 742477621981812869425111

theorem tailTrace_1445970 : CollatzResearch.WordTrace tailWord_1445970 prefixEnd_1445970 742477621981812869425111 := by
  unfold tailWord_1445970
  simp only [CollatzResearch.WordTrace]
  refine ⟨13184714642876279215063841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35159239047670077906836909 13184714642876279215063841)
  ·
    refine ⟨9888535982157209411297881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13184714642876279215063841 9888535982157209411297881)
    ·
      refine ⟨7416401986617907058473411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9888535982157209411297881 7416401986617907058473411)
      ·
        refine ⟨11124602979926860587710117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7416401986617907058473411 11124602979926860587710117)
        ·
          refine ⟨2085863058736286360195647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11124602979926860587710117 2085863058736286360195647)
          ·
            refine ⟨3128794588104429540293471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2085863058736286360195647 3128794588104429540293471)
            ·
              refine ⟨4693191882156644310440207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3128794588104429540293471 4693191882156644310440207)
              ·
                refine ⟨7039787823234966465660311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4693191882156644310440207 7039787823234966465660311)
                ·
                  refine ⟨10559681734852449698490467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7039787823234966465660311 10559681734852449698490467)
                  ·
                    refine ⟨15839522602278674547735701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10559681734852449698490467 15839522602278674547735701)
                    ·
                      refine ⟨742477621981812869425111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15839522602278674547735701 742477621981812869425111)
                      ·
                        rfl

theorem cell23_1445970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 1, 1, 6].length) (baseStart_1445970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1445970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1445970 prefixEnd_1445970 := by exact prefixLift 1445970
  have htrace : WordTrace (prefixWord ++ tailWord_1445970) baseStart_1445970 baseEnd_1445970 := by
    simpa [prefixWord, tailWord_1445970, baseEnd_1445970] using wordTrace_append hprefix tailTrace_1445970
  have hstable : (prefixWord ++ tailWord_1445970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445970).length < 2 ^ (prefixWord ++ tailWord_1445970).sum := by decide
  have hdescent : baseEnd_1445970 < baseStart_1445970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445974 : List Nat := [5, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4]
def baseStart_1445974 : Nat := 118140960795 + 1445974 * 2 ^ 59
def prefixEnd_1445974 : Nat := 4983230072969 + 3 ^ 40 * 1445974 * 2
def baseEnd_1445974 : Nat := 742479675904430853775093

theorem tailTrace_1445974 : CollatzResearch.WordTrace tailWord_1445974 prefixEnd_1445974 742479675904430853775093 := by
  unfold tailWord_1445974
  simp only [CollatzResearch.WordTrace]
  refine ⟨3296187778968164096462561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35159336308993750362267317 3296187778968164096462561)
  ·
    refine ⟨2472140834226123072346921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3296187778968164096462561 2472140834226123072346921)
    ·
      refine ⟨1854105625669592304260191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2472140834226123072346921 1854105625669592304260191)
      ·
        refine ⟨2781158438504388456390287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1854105625669592304260191 2781158438504388456390287)
        ·
          refine ⟨4171737657756582684585431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2781158438504388456390287 4171737657756582684585431)
          ·
            refine ⟨6257606486634874026878147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4171737657756582684585431 6257606486634874026878147)
            ·
              refine ⟨9386409729952311040317221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6257606486634874026878147 9386409729952311040317221)
              ·
                refine ⟨1759951824366058320059479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9386409729952311040317221 1759951824366058320059479)
                ·
                  refine ⟨2639927736549087480089219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1759951824366058320059479 2639927736549087480089219)
                  ·
                    refine ⟨3959891604823631220133829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2639927736549087480089219 3959891604823631220133829)
                    ·
                      refine ⟨742479675904430853775093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3959891604823631220133829 742479675904430853775093)
                      ·
                        rfl

theorem cell23_1445974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_1445974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1445974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1445974 prefixEnd_1445974 := by exact prefixLift 1445974
  have htrace : WordTrace (prefixWord ++ tailWord_1445974) baseStart_1445974 baseEnd_1445974 := by
    simpa [prefixWord, tailWord_1445974, baseEnd_1445974] using wordTrace_append hprefix tailTrace_1445974
  have hstable : (prefixWord ++ tailWord_1445974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445974).length < 2 ^ (prefixWord ++ tailWord_1445974).sum := by decide
  have hdescent : baseEnd_1445974 < baseStart_1445974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445980 : List Nat := [2, 2, 4, 1, 1, 2, 4, 7]
def baseStart_1445980 : Nat := 118140960795 + 1445980 * 2 ^ 59
def prefixEnd_1445980 : Nat := 4983230072969 + 3 ^ 40 * 1445980 * 2
def baseEnd_1445980 : Nat := 27499361362531771492595

theorem tailTrace_1445980 : CollatzResearch.WordTrace tailWord_1445980 prefixEnd_1445980 27499361362531771492595 := by
  unfold tailWord_1445980
  simp only [CollatzResearch.WordTrace]
  refine ⟨26369611650734444284059697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35159482200979259045412929 26369611650734444284059697)
  ·
    refine ⟨19777208738050833213044773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26369611650734444284059697 19777208738050833213044773)
    ·
      refine ⟨3708226638384531227445895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19777208738050833213044773 3708226638384531227445895)
      ·
        refine ⟨5562339957576796841168843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3708226638384531227445895 5562339957576796841168843)
        ·
          refine ⟨8343509936365195261753265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5562339957576796841168843 8343509936365195261753265)
          ·
            refine ⟨6257632452273896446314949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8343509936365195261753265 6257632452273896446314949)
            ·
              refine ⟨1173306084801355583684053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6257632452273896446314949 1173306084801355583684053)
              ·
                refine ⟨27499361362531771492595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1173306084801355583684053 27499361362531771492595)
                ·
                  rfl

theorem cell23_1445980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 4, 7].length) (baseStart_1445980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1445980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1445980 prefixEnd_1445980 := by exact prefixLift 1445980
  have htrace : WordTrace (prefixWord ++ tailWord_1445980) baseStart_1445980 baseEnd_1445980 := by
    simpa [prefixWord, tailWord_1445980, baseEnd_1445980] using wordTrace_append hprefix tailTrace_1445980
  have hstable : (prefixWord ++ tailWord_1445980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445980).length < 2 ^ (prefixWord ++ tailWord_1445980).sum := by decide
  have hdescent : baseEnd_1445980 < baseStart_1445980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446023 : List Nat := [1, 1, 4, 2, 1, 1, 2, 3, 2, 6]
def baseStart_1446023 : Nat := 118140960795 + 1446023 * 2 ^ 59
def prefixEnd_1446023 : Nat := 4983230072969 + 3 ^ 40 * 1446023 * 2
def baseEnd_1446023 : Nat := 247501612152167054020789

theorem tailTrace_1446023 : CollatzResearch.WordTrace tailWord_1446023 prefixEnd_1446023 247501612152167054020789 := by
  unfold tailWord_1446023
  simp only [CollatzResearch.WordTrace]
  refine ⟨52740791640313106911934723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35160527760208737941289815 52740791640313106911934723)
  ·
    refine ⟨79111187460469660367902085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52740791640313106911934723 79111187460469660367902085)
    ·
      refine ⟨14833347648838061318981641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79111187460469660367902085 14833347648838061318981641)
      ·
        refine ⟨11125010736628545989236231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14833347648838061318981641 11125010736628545989236231)
        ·
          refine ⟨16687516104942818983854347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11125010736628545989236231 16687516104942818983854347)
          ·
            refine ⟨25031274157414228475781521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16687516104942818983854347 25031274157414228475781521)
            ·
              refine ⟨18773455618060671356836141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25031274157414228475781521 18773455618060671356836141)
              ·
                refine ⟨7040045856772751758813553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18773455618060671356836141 7040045856772751758813553)
                ·
                  refine ⟨5280034392579563819110165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7040045856772751758813553 5280034392579563819110165)
                  ·
                    refine ⟨247501612152167054020789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5280034392579563819110165 247501612152167054020789)
                    ·
                      rfl

theorem cell23_1446023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 2, 6].length) (baseStart_1446023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1446023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1446023 prefixEnd_1446023 := by exact prefixLift 1446023
  have htrace : WordTrace (prefixWord ++ tailWord_1446023) baseStart_1446023 baseEnd_1446023 := by
    simpa [prefixWord, tailWord_1446023, baseEnd_1446023] using wordTrace_append hprefix tailTrace_1446023
  have hstable : (prefixWord ++ tailWord_1446023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446023).length < 2 ^ (prefixWord ++ tailWord_1446023).sum := by decide
  have hdescent : baseEnd_1446023 < baseStart_1446023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446024 : List Nat := [2, 1, 3, 4, 1, 2, 1, 3, 2, 1, 3]
def baseStart_1446024 : Nat := 118140960795 + 1446024 * 2 ^ 59
def prefixEnd_1446024 : Nat := 4983230072969 + 3 ^ 40 * 1446024 * 2
def baseEnd_1446024 : Nat := 742505349937155658149863

theorem tailTrace_1446024 : CollatzResearch.WordTrace tailWord_1446024 prefixEnd_1446024 742505349937155658149863 := by
  unfold tailWord_1446024
  simp only [CollatzResearch.WordTrace]
  refine ⟨26370414056654742041360563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35160552075539656055147417 26370414056654742041360563)
  ·
    refine ⟨39555621084982113062040845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26370414056654742041360563 39555621084982113062040845)
    ·
      refine ⟨14833357906868292398265317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39555621084982113062040845 14833357906868292398265317)
      ·
        refine ⟨2781254607537804824674747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14833357906868292398265317 2781254607537804824674747)
        ·
          refine ⟨4171881911306707237012121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2781254607537804824674747 4171881911306707237012121)
          ·
            refine ⟨3128911433480030427759091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4171881911306707237012121 3128911433480030427759091)
            ·
              refine ⟨4693367150220045641638637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3128911433480030427759091 4693367150220045641638637)
              ·
                refine ⟨1760012681332517115614489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4693367150220045641638637 1760012681332517115614489)
                ·
                  refine ⟨1320009510999387836710867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1760012681332517115614489 1320009510999387836710867)
                  ·
                    refine ⟨1980014266499081755066301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1320009510999387836710867 1980014266499081755066301)
                    ·
                      refine ⟨742505349937155658149863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1980014266499081755066301 742505349937155658149863)
                      ·
                        rfl

theorem cell23_1446024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_1446024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1446024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1446024 prefixEnd_1446024 := by exact prefixLift 1446024
  have htrace : WordTrace (prefixWord ++ tailWord_1446024) baseStart_1446024 baseEnd_1446024 := by
    simpa [prefixWord, tailWord_1446024, baseEnd_1446024] using wordTrace_append hprefix tailTrace_1446024
  have hstable : (prefixWord ++ tailWord_1446024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446024).length < 2 ^ (prefixWord ++ tailWord_1446024).sum := by decide
  have hdescent : baseEnd_1446024 < baseStart_1446024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446038 : List Nat := [5, 3, 2, 1, 1, 1, 1, 2, 1, 2, 4]
def baseStart_1446038 : Nat := 118140960795 + 1446038 * 2 ^ 59
def prefixEnd_1446038 : Nat := 4983230072969 + 3 ^ 40 * 1446038 * 2
def baseEnd_1446038 : Nat := 742512538666318603374799

theorem tailTrace_1446038 : CollatzResearch.WordTrace tailWord_1446038 prefixEnd_1446038 742512538666318603374799 := by
  unfold tailWord_1446038
  simp only [CollatzResearch.WordTrace]
  refine ⟨3296333670953672779608173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35160892490172509649153845 3296333670953672779608173)
  ·
    refine ⟨1236125126607627292353065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3296333670953672779608173 1236125126607627292353065)
    ·
      refine ⟨927093844955720469264799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1236125126607627292353065 927093844955720469264799)
      ·
        refine ⟨1390640767433580703897199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 927093844955720469264799 1390640767433580703897199)
        ·
          refine ⟨2085961151150371055845799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1390640767433580703897199 2085961151150371055845799)
          ·
            refine ⟨3128941726725556583768699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2085961151150371055845799 3128941726725556583768699)
            ·
              refine ⟨4693412590088334875653049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3128941726725556583768699 4693412590088334875653049)
              ·
                refine ⟨3520059442566251156739787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4693412590088334875653049 3520059442566251156739787)
                ·
                  refine ⟨5280089163849376735109681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3520059442566251156739787 5280089163849376735109681)
                  ·
                    refine ⟨3960066872887032551332261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5280089163849376735109681 3960066872887032551332261)
                    ·
                      refine ⟨742512538666318603374799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3960066872887032551332261 742512538666318603374799)
                      ·
                        rfl

theorem cell23_1446038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_1446038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1446038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1446038 prefixEnd_1446038 := by exact prefixLift 1446038
  have htrace : WordTrace (prefixWord ++ tailWord_1446038) baseStart_1446038 baseEnd_1446038 := by
    simpa [prefixWord, tailWord_1446038, baseEnd_1446038] using wordTrace_append hprefix tailTrace_1446038
  have hstable : (prefixWord ++ tailWord_1446038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446038).length < 2 ^ (prefixWord ++ tailWord_1446038).sum := by decide
  have hdescent : baseEnd_1446038 < baseStart_1446038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446047 : List Nat := [1, 1, 2, 6, 1, 1, 1, 1, 3, 4, 2]
def baseStart_1446047 : Nat := 118140960795 + 1446047 * 2 ^ 59
def prefixEnd_1446047 : Nat := 4983230072969 + 3 ^ 40 * 1446047 * 2
def baseEnd_1446047 : Nat := 742517159992209068162257

theorem tailTrace_1446047 : CollatzResearch.WordTrace tailWord_1446047 prefixEnd_1446047 742517159992209068162257 := by
  unfold tailWord_1446047
  simp only [CollatzResearch.WordTrace]
  refine ⟨52741666992226159010808395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35161111328150772673872263 52741666992226159010808395)
  ·
    refine ⟨79112500488339238516212593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52741666992226159010808395 79112500488339238516212593)
    ·
      refine ⟨59334375366254428887159445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79112500488339238516212593 59334375366254428887159445)
      ·
        refine ⟨2781298845293176354085599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 59334375366254428887159445 2781298845293176354085599)
        ·
          refine ⟨4171948267939764531128399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2781298845293176354085599 4171948267939764531128399)
          ·
            refine ⟨6257922401909646796692599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4171948267939764531128399 6257922401909646796692599)
            ·
              refine ⟨9386883602864470195038899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6257922401909646796692599 9386883602864470195038899)
              ·
                refine ⟨14080325404296705292558349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9386883602864470195038899 14080325404296705292558349)
                ·
                  refine ⟨5280122026611264484709381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14080325404296705292558349 5280122026611264484709381)
                  ·
                    refine ⟨990022879989612090883009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5280122026611264484709381 990022879989612090883009)
                    ·
                      refine ⟨742517159992209068162257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 990022879989612090883009 742517159992209068162257)
                      ·
                        rfl

theorem cell23_1446047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_1446047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1446047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1446047 prefixEnd_1446047 := by exact prefixLift 1446047
  have htrace : WordTrace (prefixWord ++ tailWord_1446047) baseStart_1446047 baseEnd_1446047 := by
    simpa [prefixWord, tailWord_1446047, baseEnd_1446047] using wordTrace_append hprefix tailTrace_1446047
  have hstable : (prefixWord ++ tailWord_1446047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446047).length < 2 ^ (prefixWord ++ tailWord_1446047).sum := by decide
  have hdescent : baseEnd_1446047 < baseStart_1446047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446080 : List Nat := [2, 1, 1, 2, 5, 1, 1, 1, 1, 5, 3]
def baseStart_1446080 : Nat := 118140960795 + 1446080 * 2 ^ 59
def prefixEnd_1446080 : Nat := 4983230072969 + 3 ^ 40 * 1446080 * 2
def baseEnd_1446080 : Nat := 742534104853807439049605

theorem tailTrace_1446080 : CollatzResearch.WordTrace tailWord_1446080 prefixEnd_1446080 742534104853807439049605 := by
  unfold tailWord_1446080
  simp only [CollatzResearch.WordTrace]
  refine ⟨26371435300553302823379847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35161913734071070431173129 26371435300553302823379847)
  ·
    refine ⟨39557152950829954235069771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26371435300553302823379847 39557152950829954235069771)
    ·
      refine ⟨59335729426244931352604657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39557152950829954235069771 59335729426244931352604657)
      ·
        refine ⟨44501797069683698514453493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59335729426244931352604657 44501797069683698514453493)
        ·
          refine ⟨4172043475282846735730015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44501797069683698514453493 4172043475282846735730015)
          ·
            refine ⟨6258065212924270103595023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4172043475282846735730015 6258065212924270103595023)
            ·
              refine ⟨9387097819386405155392535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6258065212924270103595023 9387097819386405155392535)
              ·
                refine ⟨14080646729079607733088803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9387097819386405155392535 14080646729079607733088803)
                ·
                  refine ⟨21120970093619411599633205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14080646729079607733088803 21120970093619411599633205)
                  ·
                    refine ⟨1980090946276819837465613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21120970093619411599633205 1980090946276819837465613)
                    ·
                      refine ⟨742534104853807439049605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1980090946276819837465613 742534104853807439049605)
                      ·
                        rfl

theorem cell23_1446080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 1, 5, 3].length) (baseStart_1446080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1446080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1446080 prefixEnd_1446080 := by exact prefixLift 1446080
  have htrace : WordTrace (prefixWord ++ tailWord_1446080) baseStart_1446080 baseEnd_1446080 := by
    simpa [prefixWord, tailWord_1446080, baseEnd_1446080] using wordTrace_append hprefix tailTrace_1446080
  have hstable : (prefixWord ++ tailWord_1446080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446080).length < 2 ^ (prefixWord ++ tailWord_1446080).sum := by decide
  have hdescent : baseEnd_1446080 < baseStart_1446080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446081 : List Nat := [1, 2, 6, 1, 2, 1, 2, 1, 1, 4, 2]
def baseStart_1446081 : Nat := 118140960795 + 1446081 * 2 ^ 59
def prefixEnd_1446081 : Nat := 4983230072969 + 3 ^ 40 * 1446081 * 2
def baseEnd_1446081 : Nat := 742534618334461935137101

theorem tailTrace_1446081 : CollatzResearch.WordTrace tailWord_1446081 prefixEnd_1446081 742534618334461935137101 := by
  unfold tailWord_1446081
  simp only [CollatzResearch.WordTrace]
  refine ⟨52742907074102982817546097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35161938049401988545030731 52742907074102982817546097)
  ·
    refine ⟨39557180305577237113159573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52742907074102982817546097 39557180305577237113159573)
    ·
      refine ⟨1854242826823932989679355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 39557180305577237113159573 1854242826823932989679355)
      ·
        refine ⟨2781364240235899484519033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1854242826823932989679355 2781364240235899484519033)
        ·
          refine ⟨2086023180176924613389275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2781364240235899484519033 2086023180176924613389275)
          ·
            refine ⟨3129034770265386920083913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2086023180176924613389275 3129034770265386920083913)
            ·
              refine ⟨2346776077699040190062935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3129034770265386920083913 2346776077699040190062935)
              ·
                refine ⟨3520164116548560285094403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2346776077699040190062935 3520164116548560285094403)
                ·
                  refine ⟨5280246174822840427641605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3520164116548560285094403 5280246174822840427641605)
                  ·
                    refine ⟨990046157779282580182801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5280246174822840427641605 990046157779282580182801)
                    ·
                      refine ⟨742534618334461935137101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 990046157779282580182801 742534618334461935137101)
                      ·
                        rfl

theorem cell23_1446081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_1446081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1446081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1446081 prefixEnd_1446081 := by exact prefixLift 1446081
  have htrace : WordTrace (prefixWord ++ tailWord_1446081) baseStart_1446081 baseEnd_1446081 := by
    simpa [prefixWord, tailWord_1446081, baseEnd_1446081] using wordTrace_append hprefix tailTrace_1446081
  have hstable : (prefixWord ++ tailWord_1446081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446081).length < 2 ^ (prefixWord ++ tailWord_1446081).sum := by decide
  have hdescent : baseEnd_1446081 < baseStart_1446081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446115 : List Nat := [1, 1, 1, 8, 2, 1, 1, 2, 2, 2, 2]
def baseStart_1446115 : Nat := 118140960795 + 1446115 * 2 ^ 59
def prefixEnd_1446115 : Nat := 4983230072969 + 3 ^ 40 * 1446115 * 2
def baseEnd_1446115 : Nat := 742552076676714802111945

theorem tailTrace_1446115 : CollatzResearch.WordTrace tailWord_1446115 prefixEnd_1446115 742552076676714802111945 := by
  unfold tailWord_1446115
  simp only [CollatzResearch.WordTrace]
  refine ⟨52744147155979806624283799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35162764770653204416189199 52744147155979806624283799)
  ·
    refine ⟨79116220733969709936425699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52744147155979806624283799 79116220733969709936425699)
    ·
      refine ⟨118674331100954564904638549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79116220733969709936425699 118674331100954564904638549)
      ·
        refine ⟨1390714817589311307476233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 118674331100954564904638549 1390714817589311307476233)
        ·
          refine ⟨1043036113191983480607175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1390714817589311307476233 1043036113191983480607175)
          ·
            refine ⟨1564554169787975220910763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1043036113191983480607175 1564554169787975220910763)
            ·
              refine ⟨2346831254681962831366145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1564554169787975220910763 2346831254681962831366145)
              ·
                refine ⟨1760123441011472123524609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2346831254681962831366145 1760123441011472123524609)
                ·
                  refine ⟨1320092580758604092643457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1760123441011472123524609 1320092580758604092643457)
                  ·
                    refine ⟨990069435568953069482593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1320092580758604092643457 990069435568953069482593)
                    ·
                      refine ⟨742552076676714802111945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 990069435568953069482593 742552076676714802111945)
                      ·
                        rfl

theorem cell23_1446115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_1446115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1446115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1446115 prefixEnd_1446115 := by exact prefixLift 1446115
  have htrace : WordTrace (prefixWord ++ tailWord_1446115) baseStart_1446115 baseEnd_1446115 := by
    simpa [prefixWord, tailWord_1446115, baseEnd_1446115] using wordTrace_append hprefix tailTrace_1446115
  have hstable : (prefixWord ++ tailWord_1446115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446115).length < 2 ^ (prefixWord ++ tailWord_1446115).sum := by decide
  have hdescent : baseEnd_1446115 < baseStart_1446115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446181 : List Nat := [1, 3, 1, 2, 6, 1, 1, 1, 3, 4]
def baseStart_1446181 : Nat := 118140960795 + 1446181 * 2 ^ 59
def prefixEnd_1446181 : Nat := 4983230072969 + 3 ^ 40 * 1446181 * 2
def baseEnd_1446181 : Nat := 247528655466637181295547

theorem tailTrace_1446181 : CollatzResearch.WordTrace tailWord_1446181 prefixEnd_1446181 247528655466637181295547 := by
  unfold tailWord_1446181
  simp only [CollatzResearch.WordTrace]
  refine ⟨52746554373740699896186397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35164369582493799930790931 52746554373740699896186397)
  ·
    refine ⟨19779957890152762461069899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52746554373740699896186397 19779957890152762461069899)
    ·
      refine ⟨29669936835229143691604849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19779957890152762461069899 29669936835229143691604849)
      ·
        refine ⟨22252452626421857768703637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29669936835229143691604849 22252452626421857768703637)
        ·
          refine ⟨1043083716863524582907983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 22252452626421857768703637 1043083716863524582907983)
          ·
            refine ⟨1564625575295286874361975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1043083716863524582907983 1564625575295286874361975)
            ·
              refine ⟨2346938362942930311542963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1564625575295286874361975 2346938362942930311542963)
              ·
                refine ⟨3520407544414395467314445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2346938362942930311542963 3520407544414395467314445)
                ·
                  refine ⟨1320152829155398300242917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3520407544414395467314445 1320152829155398300242917)
                  ·
                    refine ⟨247528655466637181295547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1320152829155398300242917 247528655466637181295547)
                    ·
                      rfl

theorem cell23_1446181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 1, 3, 4].length) (baseStart_1446181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1446181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1446181 prefixEnd_1446181 := by exact prefixLift 1446181
  have htrace : WordTrace (prefixWord ++ tailWord_1446181) baseStart_1446181 baseEnd_1446181 := by
    simpa [prefixWord, tailWord_1446181, baseEnd_1446181] using wordTrace_append hprefix tailTrace_1446181
  have hstable : (prefixWord ++ tailWord_1446181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446181).length < 2 ^ (prefixWord ++ tailWord_1446181).sum := by decide
  have hdescent : baseEnd_1446181 < baseStart_1446181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446224 : List Nat := [2, 1, 1, 1, 1, 7, 3, 1, 1, 5]
def baseStart_1446224 : Nat := 118140960795 + 1446224 * 2 ^ 59
def prefixEnd_1446224 : Nat := 4983230072969 + 3 ^ 40 * 1446224 * 2
def baseEnd_1446224 : Nat := 247536015356018291882981

theorem tailTrace_1446224 : CollatzResearch.WordTrace tailWord_1446224 prefixEnd_1446224 247536015356018291882981 := by
  unfold tailWord_1446224
  simp only [CollatzResearch.WordTrace]
  refine ⟨26374061356292459120000863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35165415141723278826667817 26374061356292459120000863)
  ·
    refine ⟨39561092034438688680001295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26374061356292459120000863 39561092034438688680001295)
    ·
      refine ⟨59341638051658033020001943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39561092034438688680001295 59341638051658033020001943)
      ·
        refine ⟨89012457077487049530002915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59341638051658033020001943 89012457077487049530002915)
        ·
          refine ⟨133518685616230574295004373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89012457077487049530002915 133518685616230574295004373)
          ·
            refine ⟨3129344194130404085039165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 133518685616230574295004373 3129344194130404085039165)
            ·
              refine ⟨1173504072798901531889687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3129344194130404085039165 1173504072798901531889687)
              ·
                refine ⟨1760256109198352297834531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1173504072798901531889687 1760256109198352297834531)
                ·
                  refine ⟨2640384163797528446751797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1760256109198352297834531 2640384163797528446751797)
                  ·
                    refine ⟨247536015356018291882981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2640384163797528446751797 247536015356018291882981)
                    ·
                      rfl

theorem cell23_1446224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 3, 1, 1, 5].length) (baseStart_1446224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1446224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1446224 prefixEnd_1446224 := by exact prefixLift 1446224
  have htrace : WordTrace (prefixWord ++ tailWord_1446224) baseStart_1446224 baseEnd_1446224 := by
    simpa [prefixWord, tailWord_1446224, baseEnd_1446224] using wordTrace_append hprefix tailTrace_1446224
  have hstable : (prefixWord ++ tailWord_1446224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446224).length < 2 ^ (prefixWord ++ tailWord_1446224).sum := by decide
  have hdescent : baseEnd_1446224 < baseStart_1446224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446261 : List Nat := [1, 3, 4, 1, 2, 1, 1, 1, 5, 2, 2]
def baseStart_1446261 : Nat := 118140960795 + 1446261 * 2 ^ 59
def prefixEnd_1446261 : Nat := 4983230072969 + 3 ^ 40 * 1446261 * 2
def baseEnd_1446261 : Nat := 742627044852271230886273

theorem tailTrace_1446261 : CollatzResearch.WordTrace tailWord_1446261 prefixEnd_1446261 742627044852271230886273 := by
  unfold tailWord_1446261
  simp only [CollatzResearch.WordTrace]
  refine ⟨52749472213450873559098637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35166314808967249039399091 52749472213450873559098637)
  ·
    refine ⟨19781052080044077584661989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52749472213450873559098637 19781052080044077584661989)
    ·
      refine ⟨3708947265008264547124123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19781052080044077584661989 3708947265008264547124123)
      ·
        refine ⟨5563420897512396820686185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3708947265008264547124123 5563420897512396820686185)
        ·
          refine ⟨4172565673134297615514639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5563420897512396820686185 4172565673134297615514639)
          ·
            refine ⟨6258848509701446423271959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4172565673134297615514639 6258848509701446423271959)
            ·
              refine ⟨9388272764552169634907939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6258848509701446423271959 9388272764552169634907939)
              ·
                refine ⟨14082409146828254452361909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9388272764552169634907939 14082409146828254452361909)
                ·
                  refine ⟨1320225857515148854908929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14082409146828254452361909 1320225857515148854908929)
                  ·
                    refine ⟨990169393136361641181697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1320225857515148854908929 990169393136361641181697)
                    ·
                      refine ⟨742627044852271230886273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 990169393136361641181697 742627044852271230886273)
                      ·
                        rfl

theorem cell23_1446261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 5, 2, 2].length) (baseStart_1446261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1446261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1446261 prefixEnd_1446261 := by exact prefixLift 1446261
  have htrace : WordTrace (prefixWord ++ tailWord_1446261) baseStart_1446261 baseEnd_1446261 := by
    simpa [prefixWord, tailWord_1446261, baseEnd_1446261] using wordTrace_append hprefix tailTrace_1446261
  have hstable : (prefixWord ++ tailWord_1446261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446261).length < 2 ^ (prefixWord ++ tailWord_1446261).sum := by decide
  have hdescent : baseEnd_1446261 < baseStart_1446261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446267 : List Nat := [1, 1, 1, 1, 1, 8, 3, 7]
def baseStart_1446267 : Nat := 118140960795 + 1446267 * 2 ^ 59
def prefixEnd_1446267 : Nat := 4983230072969 + 3 ^ 40 * 1446267 * 2
def baseEnd_1446267 : Nat := 27504819471711044718935

theorem tailTrace_1446267 : CollatzResearch.WordTrace tailWord_1446267 prefixEnd_1446267 27504819471711044718935 := by
  unfold tailWord_1446267
  simp only [CollatzResearch.WordTrace]
  refine ⟨52749691051429136583817055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35166460700952757722544703 52749691051429136583817055)
  ·
    refine ⟨79124536577143704875725583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52749691051429136583817055 79124536577143704875725583)
    ·
      refine ⟨118686804865715557313588375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79124536577143704875725583 118686804865715557313588375)
      ·
        refine ⟨178030207298573335970382563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118686804865715557313588375 178030207298573335970382563)
        ·
          refine ⟨267045310947860003955573845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178030207298573335970382563 267045310947860003955573845)
          ·
            refine ⟨3129437237670234421354381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 267045310947860003955573845 3129437237670234421354381)
            ·
              refine ⟨1173538964126337908007893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3129437237670234421354381 1173538964126337908007893)
              ·
                refine ⟨27504819471711044718935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1173538964126337908007893 27504819471711044718935)
                ·
                  rfl

theorem cell23_1446267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 3, 7].length) (baseStart_1446267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1446267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1446267 prefixEnd_1446267 := by exact prefixLift 1446267
  have htrace : WordTrace (prefixWord ++ tailWord_1446267) baseStart_1446267 baseEnd_1446267 := by
    simpa [prefixWord, tailWord_1446267, baseEnd_1446267] using wordTrace_append hprefix tailTrace_1446267
  have hstable : (prefixWord ++ tailWord_1446267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446267).length < 2 ^ (prefixWord ++ tailWord_1446267).sum := by decide
  have hdescent : baseEnd_1446267 < baseStart_1446267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446281 : List Nat := [1, 2, 1, 1, 6, 1, 4, 1, 1, 2, 3]
def baseStart_1446281 : Nat := 118140960795 + 1446281 * 2 ^ 59
def prefixEnd_1446281 : Nat := 4983230072969 + 3 ^ 40 * 1446281 * 2
def baseEnd_1446281 : Nat := 742637314465361152636181

theorem tailTrace_1446281 : CollatzResearch.WordTrace tailWord_1446281 prefixEnd_1446281 742637314465361152636181 := by
  unfold tailWord_1446281
  simp only [CollatzResearch.WordTrace]
  refine ⟨52750201673378416974826697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35166801115585611316551131 52750201673378416974826697)
  ·
    refine ⟨39562651255033812731120023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52750201673378416974826697 39562651255033812731120023)
    ·
      refine ⟨59343976882550719096680035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39562651255033812731120023 59343976882550719096680035)
      ·
        refine ⟨89015965323826078645020053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59343976882550719096680035 89015965323826078645020053)
        ·
          refine ⟨4172623374554347436485315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 89015965323826078645020053 4172623374554347436485315)
          ·
            refine ⟨6258935061831521154727973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4172623374554347436485315 6258935061831521154727973)
            ·
              refine ⟨1173550324093410216511495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6258935061831521154727973 1173550324093410216511495)
              ·
                refine ⟨1760325486140115324767243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1173550324093410216511495 1760325486140115324767243)
                ·
                  refine ⟨2640488229210172987150865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1760325486140115324767243 2640488229210172987150865)
                  ·
                    refine ⟨1980366171907629740363149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2640488229210172987150865 1980366171907629740363149)
                    ·
                      refine ⟨742637314465361152636181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1980366171907629740363149 742637314465361152636181)
                      ·
                        rfl

theorem cell23_1446281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 4, 1, 1, 2, 3].length) (baseStart_1446281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1446281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1446281 prefixEnd_1446281 := by exact prefixLift 1446281
  have htrace : WordTrace (prefixWord ++ tailWord_1446281) baseStart_1446281 baseEnd_1446281 := by
    simpa [prefixWord, tailWord_1446281, baseEnd_1446281] using wordTrace_append hprefix tailTrace_1446281
  have hstable : (prefixWord ++ tailWord_1446281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446281).length < 2 ^ (prefixWord ++ tailWord_1446281).sum := by decide
  have hdescent : baseEnd_1446281 < baseStart_1446281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446311 : List Nat := [1, 1, 6, 1, 1, 4, 1, 1, 1, 3, 3]
def baseStart_1446311 : Nat := 118140960795 + 1446311 * 2 ^ 59
def prefixEnd_1446311 : Nat := 4983230072969 + 3 ^ 40 * 1446311 * 2
def baseEnd_1446311 : Nat := 742652718884996035261043

theorem tailTrace_1446311 : CollatzResearch.WordTrace tailWord_1446311 prefixEnd_1446311 742652718884996035261043 := by
  unfold tailWord_1446311
  simp only [CollatzResearch.WordTrace]
  refine ⟨52751295863269732098418787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35167530575513154732279191 52751295863269732098418787)
  ·
    refine ⟨79126943794904598147628181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52751295863269732098418787 79126943794904598147628181)
    ·
      refine ⟨3709075490386153038170071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 79126943794904598147628181 3709075490386153038170071)
      ·
        refine ⟨5563613235579229557255107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3709075490386153038170071 5563613235579229557255107)
        ·
          refine ⟨8345419853368844335882661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5563613235579229557255107 8345419853368844335882661)
          ·
            refine ⟨1564766222506658312977999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8345419853368844335882661 1564766222506658312977999)
            ·
              refine ⟨2347149333759987469466999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1564766222506658312977999 2347149333759987469466999)
              ·
                refine ⟨3520724000639981204200499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2347149333759987469466999 3520724000639981204200499)
                ·
                  refine ⟨5281086000959971806300749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3520724000639981204200499 5281086000959971806300749)
                  ·
                    refine ⟨1980407250359989427362781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5281086000959971806300749 1980407250359989427362781)
                    ·
                      refine ⟨742652718884996035261043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1980407250359989427362781 742652718884996035261043)
                      ·
                        rfl

theorem cell23_1446311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_1446311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1446311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1446311 prefixEnd_1446311 := by exact prefixLift 1446311
  have htrace : WordTrace (prefixWord ++ tailWord_1446311) baseStart_1446311 baseEnd_1446311 := by
    simpa [prefixWord, tailWord_1446311, baseEnd_1446311] using wordTrace_append hprefix tailTrace_1446311
  have hstable : (prefixWord ++ tailWord_1446311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446311).length < 2 ^ (prefixWord ++ tailWord_1446311).sum := by decide
  have hdescent : baseEnd_1446311 < baseStart_1446311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446321 : List Nat := [1, 2, 2, 4, 1, 2, 1, 4, 1, 3, 2]
def baseStart_1446321 : Nat := 118140960795 + 1446321 * 2 ^ 59
def prefixEnd_1446321 : Nat := 4983230072969 + 3 ^ 40 * 1446321 * 2
def baseEnd_1446321 : Nat := 742657853691540996135997

theorem tailTrace_1446321 : CollatzResearch.WordTrace tailWord_1446321 prefixEnd_1446321 742657853691540996135997 := by
  unfold tailWord_1446321
  simp only [CollatzResearch.WordTrace]
  refine ⟨52751660593233503806282817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35167773728822335870855211 52751660593233503806282817)
  ·
    refine ⟨39563745444925127854712113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52751660593233503806282817 39563745444925127854712113)
    ·
      refine ⟨29672809083693845891034085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39563745444925127854712113 29672809083693845891034085)
      ·
        refine ⟨5563651703192596104568891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29672809083693845891034085 5563651703192596104568891)
        ·
          refine ⟨8345477554788894156853337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5563651703192596104568891 8345477554788894156853337)
          ·
            refine ⟨6259108166091670617640003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8345477554788894156853337 6259108166091670617640003)
            ·
              refine ⟨9388662249137505926460005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6259108166091670617640003 9388662249137505926460005)
              ·
                refine ⟨1760374171713282361211251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9388662249137505926460005 1760374171713282361211251)
                ·
                  refine ⟨2640561257569923541816877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1760374171713282361211251 2640561257569923541816877)
                  ·
                    refine ⟨990210471588721328181329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2640561257569923541816877 990210471588721328181329)
                    ·
                      refine ⟨742657853691540996135997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 990210471588721328181329 742657853691540996135997)
                      ·
                        rfl

theorem cell23_1446321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 4, 1, 3, 2].length) (baseStart_1446321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1446321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1446321 prefixEnd_1446321 := by exact prefixLift 1446321
  have htrace : WordTrace (prefixWord ++ tailWord_1446321) baseStart_1446321 baseEnd_1446321 := by
    simpa [prefixWord, tailWord_1446321, baseEnd_1446321] using wordTrace_append hprefix tailTrace_1446321
  have hstable : (prefixWord ++ tailWord_1446321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446321).length < 2 ^ (prefixWord ++ tailWord_1446321).sum := by decide
  have hdescent : baseEnd_1446321 < baseStart_1446321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446351 : List Nat := [1, 1, 2, 1, 1, 4, 1, 6, 2, 2, 2]
def baseStart_1446351 : Nat := 118140960795 + 1446351 * 2 ^ 59
def prefixEnd_1446351 : Nat := 4983230072969 + 3 ^ 40 * 1446351 * 2
def baseEnd_1446351 : Nat := 742673258111175878760859

theorem tailTrace_1446351 : CollatzResearch.WordTrace tailWord_1446351 prefixEnd_1446351 742673258111175878760859 := by
  unfold tailWord_1446351
  simp only [CollatzResearch.WordTrace]
  refine ⟨52752754783124818929874907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35168503188749879286583271 52752754783124818929874907)
  ·
    refine ⟨79129132174687228394812361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52752754783124818929874907 79129132174687228394812361)
    ·
      refine ⟨59346849131015421296109271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79129132174687228394812361 59346849131015421296109271)
      ·
        refine ⟨89020273696523131944163907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59346849131015421296109271 89020273696523131944163907)
        ·
          refine ⟨133530410544784697916245861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89020273696523131944163907 133530410544784697916245861)
          ·
            refine ⟨25036951977147130859296099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 133530410544784697916245861 25036951977147130859296099)
            ·
              refine ⟨37555427965720696288944149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25036951977147130859296099 37555427965720696288944149)
              ·
                refine ⟨1760410685893157638544257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 37555427965720696288944149 1760410685893157638544257)
                ·
                  refine ⟨1320308014419868228908193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1760410685893157638544257 1320308014419868228908193)
                  ·
                    refine ⟨990231010814901171681145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1320308014419868228908193 990231010814901171681145)
                    ·
                      refine ⟨742673258111175878760859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 990231010814901171681145 742673258111175878760859)
                      ·
                        rfl

theorem cell23_1446351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 6, 2, 2, 2].length) (baseStart_1446351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1446351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1446351 prefixEnd_1446351 := by exact prefixLift 1446351
  have htrace : WordTrace (prefixWord ++ tailWord_1446351) baseStart_1446351 baseEnd_1446351 := by
    simpa [prefixWord, tailWord_1446351, baseEnd_1446351] using wordTrace_append hprefix tailTrace_1446351
  have hstable : (prefixWord ++ tailWord_1446351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446351).length < 2 ^ (prefixWord ++ tailWord_1446351).sum := by decide
  have hdescent : baseEnd_1446351 < baseStart_1446351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446397 : List Nat := [1, 4, 1, 1, 1, 3, 1, 1, 3, 2, 5]
def baseStart_1446397 : Nat := 118140960795 + 1446397 * 2 ^ 59
def prefixEnd_1446397 : Nat := 4983230072969 + 3 ^ 40 * 1446397 * 2
def baseEnd_1446397 : Nat := 742696878221282698785647

theorem tailTrace_1446397 : CollatzResearch.WordTrace tailWord_1446397 prefixEnd_1446397 742696878221282698785647 := by
  unfold tailWord_1446397
  simp only [CollatzResearch.WordTrace]
  refine ⟨52754432540958168786049445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35169621693972112524032963 52754432540958168786049445)
  ·
    refine ⟨9891456101429656647384271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52754432540958168786049445 9891456101429656647384271)
    ·
      refine ⟨14837184152144484971076407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9891456101429656647384271 14837184152144484971076407)
      ·
        refine ⟨22255776228216727456614611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14837184152144484971076407 22255776228216727456614611)
        ·
          refine ⟨33383664342325091184921917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22255776228216727456614611 33383664342325091184921917)
          ·
            refine ⟨12518874128371909194345719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33383664342325091184921917 12518874128371909194345719)
            ·
              refine ⟨18778311192557863791518579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12518874128371909194345719 18778311192557863791518579)
              ·
                refine ⟨28167466788836795687277869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18778311192557863791518579 28167466788836795687277869)
                ·
                  refine ⟨10562800045813798382729201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28167466788836795687277869 10562800045813798382729201)
                  ·
                    refine ⟨7922100034360348787046901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10562800045813798382729201 7922100034360348787046901)
                    ·
                      refine ⟨742696878221282698785647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7922100034360348787046901 742696878221282698785647)
                      ·
                        rfl

theorem cell23_1446397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 2, 5].length) (baseStart_1446397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1446397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1446397 prefixEnd_1446397 := by exact prefixLift 1446397
  have htrace : WordTrace (prefixWord ++ tailWord_1446397) baseStart_1446397 baseEnd_1446397 := by
    simpa [prefixWord, tailWord_1446397, baseEnd_1446397] using wordTrace_append hprefix tailTrace_1446397
  have hstable : (prefixWord ++ tailWord_1446397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446397).length < 2 ^ (prefixWord ++ tailWord_1446397).sum := by decide
  have hdescent : baseEnd_1446397 < baseStart_1446397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446402 : List Nat := [3, 4, 1, 2, 2, 1, 2, 2, 2, 2, 2]
def baseStart_1446402 : Nat := 118140960795 + 1446402 * 2 ^ 59
def prefixEnd_1446402 : Nat := 4983230072969 + 3 ^ 40 * 1446402 * 2
def baseEnd_1446402 : Nat := 742699445624555179223125

theorem tailTrace_1446402 : CollatzResearch.WordTrace tailWord_1446402 prefixEnd_1446402 742699445624555179223125 := by
  unfold tailWord_1446402
  simp only [CollatzResearch.WordTrace]
  refine ⟨13188653726485013659995365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35169743270626703093320973 13188653726485013659995365)
  ·
    refine ⟨2472872573715940061249131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13188653726485013659995365 2472872573715940061249131)
    ·
      refine ⟨3709308860573910091873697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2472872573715940061249131 3709308860573910091873697)
      ·
        refine ⟨2781981645430432568905273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3709308860573910091873697 2781981645430432568905273)
        ·
          refine ⟨2086486234072824426678955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2781981645430432568905273 2086486234072824426678955)
          ·
            refine ⟨3129729351109236640018433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2086486234072824426678955 3129729351109236640018433)
            ·
              refine ⟨2347297013331927480013825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3129729351109236640018433 2347297013331927480013825)
              ·
                refine ⟨1760472759998945610010369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2347297013331927480013825 1760472759998945610010369)
                ·
                  refine ⟨1320354569999209207507777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1760472759998945610010369 1320354569999209207507777)
                  ·
                    refine ⟨990265927499406905630833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1320354569999209207507777 990265927499406905630833)
                    ·
                      refine ⟨742699445624555179223125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 990265927499406905630833 742699445624555179223125)
                      ·
                        rfl

theorem cell23_1446402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_1446402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1446402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1446402 prefixEnd_1446402 := by exact prefixLift 1446402
  have htrace : WordTrace (prefixWord ++ tailWord_1446402) baseStart_1446402 baseEnd_1446402 := by
    simpa [prefixWord, tailWord_1446402, baseEnd_1446402] using wordTrace_append hprefix tailTrace_1446402
  have hstable : (prefixWord ++ tailWord_1446402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446402).length < 2 ^ (prefixWord ++ tailWord_1446402).sum := by decide
  have hdescent : baseEnd_1446402 < baseStart_1446402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446414 : List Nat := [4, 1, 1, 2, 3, 1, 2, 1, 1, 2, 5]
def baseStart_1446414 : Nat := 118140960795 + 1446414 * 2 ^ 59
def prefixEnd_1446414 : Nat := 4983230072969 + 3 ^ 40 * 1446414 * 2
def baseEnd_1446414 : Nat := 742705607392409132273069

theorem tailTrace_1446414 : CollatzResearch.WordTrace tailWord_1446414 prefixEnd_1446414 742705607392409132273069 := by
  unfold tailWord_1446414
  simp only [CollatzResearch.WordTrace]
  refine ⟨6594381572737072586177287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35170035054597720459612197 6594381572737072586177287)
  ·
    refine ⟨9891572359105608879265931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6594381572737072586177287 9891572359105608879265931)
    ·
      refine ⟨14837358538658413318898897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9891572359105608879265931 14837358538658413318898897)
      ·
        refine ⟨11128018903993809989174173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14837358538658413318898897 11128018903993809989174173)
        ·
          refine ⟨4173007088997678745940315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11128018903993809989174173 4173007088997678745940315)
          ·
            refine ⟨6259510633496518118910473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4173007088997678745940315 6259510633496518118910473)
            ·
              refine ⟨4694632975122388589182855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6259510633496518118910473 4694632975122388589182855)
              ·
                refine ⟨7041949462683582883774283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4694632975122388589182855 7041949462683582883774283)
                ·
                  refine ⟨10562924194025374325661425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7041949462683582883774283 10562924194025374325661425)
                  ·
                    refine ⟨7922193145519030744246069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10562924194025374325661425 7922193145519030744246069)
                    ·
                      refine ⟨742705607392409132273069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7922193145519030744246069 742705607392409132273069)
                      ·
                        rfl

theorem cell23_1446414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_1446414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1446414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1446414 prefixEnd_1446414 := by exact prefixLift 1446414
  have htrace : WordTrace (prefixWord ++ tailWord_1446414) baseStart_1446414 baseEnd_1446414 := by
    simpa [prefixWord, tailWord_1446414, baseEnd_1446414] using wordTrace_append hprefix tailTrace_1446414
  have hstable : (prefixWord ++ tailWord_1446414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446414).length < 2 ^ (prefixWord ++ tailWord_1446414).sum := by decide
  have hdescent : baseEnd_1446414 < baseStart_1446414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446464 : List Nat := [2, 1, 1, 2, 2, 2, 5, 2, 6]
def baseStart_1446464 : Nat := 118140960795 + 1446464 * 2 ^ 59
def prefixEnd_1446464 : Nat := 4983230072969 + 3 ^ 40 * 1446464 * 2
def baseEnd_1446464 : Nat := 82525697936125992960871

theorem tailTrace_1446464 : CollatzResearch.WordTrace tailWord_1446464 prefixEnd_1446464 82525697936125992960871 := by
  unfold tailWord_1446464
  simp only [CollatzResearch.WordTrace]
  refine ⟨26378438115857719614369223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35171250821143626152492297 26378438115857719614369223)
  ·
    refine ⟨39567657173786579421553835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26378438115857719614369223 39567657173786579421553835)
    ·
      refine ⟨59351485760679869132330753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39567657173786579421553835 59351485760679869132330753)
      ·
        refine ⟨44513614320509901849248065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59351485760679869132330753 44513614320509901849248065)
        ·
          refine ⟨33385210740382426386936049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44513614320509901849248065 33385210740382426386936049)
          ·
            refine ⟨25038908055286819790202037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33385210740382426386936049 25038908055286819790202037)
            ·
              refine ⟨2347397630183139355331441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25038908055286819790202037 2347397630183139355331441)
              ·
                refine ⟨1760548222637354516498581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2347397630183139355331441 1760548222637354516498581)
                ·
                  refine ⟨82525697936125992960871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1760548222637354516498581 82525697936125992960871)
                  ·
                    rfl

theorem cell23_1446464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 2, 6].length) (baseStart_1446464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1446464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1446464 prefixEnd_1446464 := by exact prefixLift 1446464
  have htrace : WordTrace (prefixWord ++ tailWord_1446464) baseStart_1446464 baseEnd_1446464 := by
    simpa [prefixWord, tailWord_1446464, baseEnd_1446464] using wordTrace_append hprefix tailTrace_1446464
  have hstable : (prefixWord ++ tailWord_1446464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446464).length < 2 ^ (prefixWord ++ tailWord_1446464).sum := by decide
  have hdescent : baseEnd_1446464 < baseStart_1446464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446481 : List Nat := [1, 2, 2, 1, 3, 4, 3, 1, 6]
def baseStart_1446481 : Nat := 118140960795 + 1446481 * 2 ^ 59
def prefixEnd_1446481 : Nat := 4983230072969 + 3 ^ 40 * 1446481 * 2
def baseEnd_1446481 : Nat := 82526667844028930015029

theorem tailTrace_1446481 : CollatzResearch.WordTrace tailWord_1446481 prefixEnd_1446481 82526667844028930015029 := by
  unfold tailWord_1446481
  simp only [CollatzResearch.WordTrace]
  refine ⟨52757496272653851132107297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35171664181769234088071531 52757496272653851132107297)
  ·
    refine ⟨39568122204490388349080473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52757496272653851132107297 39568122204490388349080473)
    ·
      refine ⟨29676091653367791261810355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39568122204490388349080473 29676091653367791261810355)
      ·
        refine ⟨44514137480051686892715533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29676091653367791261810355 44514137480051686892715533)
        ·
          refine ⟨16692801555019382584768325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44514137480051686892715533 16692801555019382584768325)
          ·
            refine ⟨3129900291566134234644061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16692801555019382584768325 3129900291566134234644061)
            ·
              refine ⟨1173712609337300337991523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3129900291566134234644061 1173712609337300337991523)
              ·
                refine ⟨1760568914005950506987285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1173712609337300337991523 1760568914005950506987285)
                ·
                  refine ⟨82526667844028930015029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1760568914005950506987285 82526667844028930015029)
                  ·
                    rfl

theorem cell23_1446481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 3, 1, 6].length) (baseStart_1446481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1446481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1446481 prefixEnd_1446481 := by exact prefixLift 1446481
  have htrace : WordTrace (prefixWord ++ tailWord_1446481) baseStart_1446481 baseEnd_1446481 := by
    simpa [prefixWord, tailWord_1446481, baseEnd_1446481] using wordTrace_append hprefix tailTrace_1446481
  have hstable : (prefixWord ++ tailWord_1446481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446481).length < 2 ^ (prefixWord ++ tailWord_1446481).sum := by decide
  have hdescent : baseEnd_1446481 < baseStart_1446481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446525 : List Nat := [1, 4, 1, 1, 5, 2, 1, 1, 3, 1, 3]
def baseStart_1446525 : Nat := 118140960795 + 1446525 * 2 ^ 59
def prefixEnd_1446525 : Nat := 4983230072969 + 3 ^ 40 * 1446525 * 2
def baseEnd_1446525 : Nat := 742762603745058197985059

theorem tailTrace_1446525 : CollatzResearch.WordTrace tailWord_1446525 prefixEnd_1446525 742762603745058197985059 := by
  unfold tailWord_1446525
  simp only [CollatzResearch.WordTrace]
  refine ⟨52759101084494446646709029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35172734056329631097806019 52759101084494446646709029)
  ·
    refine ⟨9892331453342708746257943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52759101084494446646709029 9892331453342708746257943)
    ·
      refine ⟨14838497180014063119386915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9892331453342708746257943 14838497180014063119386915)
      ·
        refine ⟨22257745770021094679080373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14838497180014063119386915 22257745770021094679080373)
        ·
          refine ⟨2086663665939477626163785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22257745770021094679080373 2086663665939477626163785)
          ·
            refine ⟨1564997749454608219622839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2086663665939477626163785 1564997749454608219622839)
            ·
              refine ⟨2347496624181912329434259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1564997749454608219622839 2347496624181912329434259)
              ·
                refine ⟨3521244936272868494151389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2347496624181912329434259 3521244936272868494151389)
                ·
                  refine ⟨1320466851102325685306771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3521244936272868494151389 1320466851102325685306771)
                  ·
                    refine ⟨1980700276653488527960157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1320466851102325685306771 1980700276653488527960157)
                    ·
                      refine ⟨742762603745058197985059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1980700276653488527960157 742762603745058197985059)
                      ·
                        rfl

theorem cell23_1446525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 1, 3, 1, 3].length) (baseStart_1446525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1446525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1446525 prefixEnd_1446525 := by exact prefixLift 1446525
  have htrace : WordTrace (prefixWord ++ tailWord_1446525) baseStart_1446525 baseEnd_1446525 := by
    simpa [prefixWord, tailWord_1446525, baseEnd_1446525] using wordTrace_append hprefix tailTrace_1446525
  have hstable : (prefixWord ++ tailWord_1446525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446525).length < 2 ^ (prefixWord ++ tailWord_1446525).sum := by decide
  have hdescent : baseEnd_1446525 < baseStart_1446525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446548 : List Nat := [2, 4, 2, 2, 1, 2, 1, 1, 3, 1, 4]
def baseStart_1446548 : Nat := 118140960795 + 1446548 * 2 ^ 59
def prefixEnd_1446548 : Nat := 4983230072969 + 3 ^ 40 * 1446548 * 2
def baseEnd_1446548 : Nat := 742774413800111607997453

theorem tailTrace_1446548 : CollatzResearch.WordTrace tailWord_1446548 prefixEnd_1446548 742774413800111607997453 := by
  unfold tailWord_1446548
  simp only [CollatzResearch.WordTrace]
  refine ⟨26379969981705560787398149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35173293308940747716530865 26379969981705560787398149)
  ·
    refine ⟨4946244371569792647637153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26379969981705560787398149 4946244371569792647637153)
    ·
      refine ⟨3709683278677344485727865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4946244371569792647637153 3709683278677344485727865)
      ·
        refine ⟨2782262459008008364295899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3709683278677344485727865 2782262459008008364295899)
        ·
          refine ⟨4173393688512012546443849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2782262459008008364295899 4173393688512012546443849)
          ·
            refine ⟨3130045266384009409832887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4173393688512012546443849 3130045266384009409832887)
            ·
              refine ⟨4695067899576014114749331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3130045266384009409832887 4695067899576014114749331)
              ·
                refine ⟨7042601849364021172123997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4695067899576014114749331 7042601849364021172123997)
                ·
                  refine ⟨2640975693511507939546499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7042601849364021172123997 2640975693511507939546499)
                  ·
                    refine ⟨3961463540267261909319749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2640975693511507939546499 3961463540267261909319749)
                    ·
                      refine ⟨742774413800111607997453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3961463540267261909319749 742774413800111607997453)
                      ·
                        rfl

theorem cell23_1446548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_1446548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1446548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1446548 prefixEnd_1446548 := by exact prefixLift 1446548
  have htrace : WordTrace (prefixWord ++ tailWord_1446548) baseStart_1446548 baseEnd_1446548 := by
    simpa [prefixWord, tailWord_1446548, baseEnd_1446548] using wordTrace_append hprefix tailTrace_1446548
  have hstable : (prefixWord ++ tailWord_1446548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446548).length < 2 ^ (prefixWord ++ tailWord_1446548).sum := by decide
  have hdescent : baseEnd_1446548 < baseStart_1446548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446551 : List Nat := [1, 1, 3, 3, 2, 1, 3, 1, 3, 2, 3]
def baseStart_1446551 : Nat := 118140960795 + 1446551 * 2 ^ 59
def prefixEnd_1446551 : Nat := 4983230072969 + 3 ^ 40 * 1446551 * 2
def baseEnd_1446551 : Nat := 742775954242075096259939

theorem tailTrace_1446551 : CollatzResearch.WordTrace tailWord_1446551 prefixEnd_1446551 742775954242075096259939 := by
  unfold tailWord_1446551
  simp only [CollatzResearch.WordTrace]
  refine ⟨52760049382400253087155507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35173366254933502058103671 52760049382400253087155507)
  ·
    refine ⟨79140074073600379630733261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52760049382400253087155507 79140074073600379630733261)
    ·
      refine ⟨29677527777600142361524973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79140074073600379630733261 29677527777600142361524973)
      ·
        refine ⟨11129072916600053385571865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29677527777600142361524973 11129072916600053385571865)
        ·
          refine ⟨8346804687450040039178899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11129072916600053385571865 8346804687450040039178899)
          ·
            refine ⟨12520207031175060058768349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8346804687450040039178899 12520207031175060058768349)
            ·
              refine ⟨4695077636690647522038131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12520207031175060058768349 4695077636690647522038131)
              ·
                refine ⟨7042616455035971283057197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4695077636690647522038131 7042616455035971283057197)
                ·
                  refine ⟨2640981170638489231146449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7042616455035971283057197 2640981170638489231146449)
                  ·
                    refine ⟨1980735877978866923359837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2640981170638489231146449 1980735877978866923359837)
                    ·
                      refine ⟨742775954242075096259939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1980735877978866923359837 742775954242075096259939)
                      ·
                        rfl

theorem cell23_1446551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 3, 2, 3].length) (baseStart_1446551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1446551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1446551 prefixEnd_1446551 := by exact prefixLift 1446551
  have htrace : WordTrace (prefixWord ++ tailWord_1446551) baseStart_1446551 baseEnd_1446551 := by
    simpa [prefixWord, tailWord_1446551, baseEnd_1446551] using wordTrace_append hprefix tailTrace_1446551
  have hstable : (prefixWord ++ tailWord_1446551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446551).length < 2 ^ (prefixWord ++ tailWord_1446551).sum := by decide
  have hdescent : baseEnd_1446551 < baseStart_1446551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446565 : List Nat := [1, 3, 1, 2, 1, 2, 1, 7, 1, 2, 2]
def baseStart_1446565 : Nat := 118140960795 + 1446565 * 2 ^ 59
def prefixEnd_1446565 : Nat := 4983230072969 + 3 ^ 40 * 1446565 * 2
def baseEnd_1446565 : Nat := 742783142971238041484875

theorem tailTrace_1446565 : CollatzResearch.WordTrace tailWord_1446565 prefixEnd_1446565 742783142971238041484875 := by
  unfold tailWord_1446565
  simp only [CollatzResearch.WordTrace]
  refine ⟨52760560004349533478165149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35173706669566355652110099 52760560004349533478165149)
  ·
    refine ⟨19785210001631075054311931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52760560004349533478165149 19785210001631075054311931)
    ·
      refine ⟨29677815002446612581467897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19785210001631075054311931 29677815002446612581467897)
      ·
        refine ⟨22258361251834959436100923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29677815002446612581467897 22258361251834959436100923)
        ·
          refine ⟨33387541877752439154151385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22258361251834959436100923 33387541877752439154151385)
          ·
            refine ⟨25040656408314329365613539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33387541877752439154151385 25040656408314329365613539)
            ·
              refine ⟨37560984612471494048420309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25040656408314329365613539 37560984612471494048420309)
              ·
                refine ⟨880335576854800641759851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 37560984612471494048420309 880335576854800641759851)
                ·
                  refine ⟨1320503365282200962639777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 880335576854800641759851 1320503365282200962639777)
                  ·
                    refine ⟨990377523961650721979833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1320503365282200962639777 990377523961650721979833)
                    ·
                      refine ⟨742783142971238041484875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 990377523961650721979833 742783142971238041484875)
                      ·
                        rfl

theorem cell23_1446565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 7, 1, 2, 2].length) (baseStart_1446565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1446565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1446565 prefixEnd_1446565 := by exact prefixLift 1446565
  have htrace : WordTrace (prefixWord ++ tailWord_1446565) baseStart_1446565 baseEnd_1446565 := by
    simpa [prefixWord, tailWord_1446565, baseEnd_1446565] using wordTrace_append hprefix tailTrace_1446565
  have hstable : (prefixWord ++ tailWord_1446565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446565).length < 2 ^ (prefixWord ++ tailWord_1446565).sum := by decide
  have hdescent : baseEnd_1446565 < baseStart_1446565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446605 : List Nat := [1, 6, 2, 1, 2, 1, 3, 7]
def baseStart_1446605 : Nat := 118140960795 + 1446605 * 2 ^ 59
def prefixEnd_1446605 : Nat := 4983230072969 + 3 ^ 40 * 1446605 * 2
def baseEnd_1446605 : Nat := 27511247488793254999433

theorem tailTrace_1446605 : CollatzResearch.WordTrace tailWord_1446605 prefixEnd_1446605 27511247488793254999433 := by
  unfold tailWord_1446605
  simp only [CollatzResearch.WordTrace]
  refine ⟨52762018924204620309621269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35174679282803080206414179 52762018924204620309621269)
  ·
    refine ⟨2473219637072091577013497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 52762018924204620309621269 2473219637072091577013497)
    ·
      refine ⟨1854914727804068682760123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2473219637072091577013497 1854914727804068682760123)
      ·
        refine ⟨2782372091706103024140185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1854914727804068682760123 2782372091706103024140185)
        ·
          refine ⟨2086779068779577268105139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2782372091706103024140185 2086779068779577268105139)
          ·
            refine ⟨3130168603169365902157709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2086779068779577268105139 3130168603169365902157709)
            ·
              refine ⟨1173813226188512213309141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3130168603169365902157709 1173813226188512213309141)
              ·
                refine ⟨27511247488793254999433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1173813226188512213309141 27511247488793254999433)
                ·
                  rfl

theorem cell23_1446605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 3, 7].length) (baseStart_1446605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1446605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1446605 prefixEnd_1446605 := by exact prefixLift 1446605
  have htrace : WordTrace (prefixWord ++ tailWord_1446605) baseStart_1446605 baseEnd_1446605 := by
    simpa [prefixWord, tailWord_1446605, baseEnd_1446605] using wordTrace_append hprefix tailTrace_1446605
  have hstable : (prefixWord ++ tailWord_1446605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446605).length < 2 ^ (prefixWord ++ tailWord_1446605).sum := by decide
  have hdescent : baseEnd_1446605 < baseStart_1446605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446624 : List Nat := [2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 5]
def baseStart_1446624 : Nat := 118140960795 + 1446624 * 2 ^ 59
def prefixEnd_1446624 : Nat := 4983230072969 + 3 ^ 40 * 1446624 * 2
def baseEnd_1446624 : Nat := 742813438329853310647103

theorem tailTrace_1446624 : CollatzResearch.WordTrace tailWord_1446624 prefixEnd_1446624 742813438329853310647103 := by
  unfold tailWord_1446624
  simp only [CollatzResearch.WordTrace]
  refine ⟨26381355955567893277281463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35175141274090524369708617 26381355955567893277281463)
  ·
    refine ⟨39572033933351839915922195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26381355955567893277281463 39572033933351839915922195)
    ·
      refine ⟨59358050900027759873883293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39572033933351839915922195 59358050900027759873883293)
      ·
        refine ⟨22259269087510409952706235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59358050900027759873883293 22259269087510409952706235)
        ·
          refine ⟨33388903631265614929059353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22259269087510409952706235 33388903631265614929059353)
          ·
            refine ⟨25041677723449211196794515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33388903631265614929059353 25041677723449211196794515)
            ·
              refine ⟨37562516585173816795191773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25041677723449211196794515 37562516585173816795191773)
              ·
                refine ⟨14085943719440181298196915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37562516585173816795191773 14085943719440181298196915)
                ·
                  refine ⟨21128915579160271947295373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14085943719440181298196915 21128915579160271947295373)
                  ·
                    refine ⟨7923343342185101980235765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21128915579160271947295373 7923343342185101980235765)
                    ·
                      refine ⟨742813438329853310647103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7923343342185101980235765 742813438329853310647103)
                      ·
                        rfl

theorem cell23_1446624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 5].length) (baseStart_1446624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1446624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1446624 prefixEnd_1446624 := by exact prefixLift 1446624
  have htrace : WordTrace (prefixWord ++ tailWord_1446624) baseStart_1446624 baseEnd_1446624 := by
    simpa [prefixWord, tailWord_1446624, baseEnd_1446624] using wordTrace_append hprefix tailTrace_1446624
  have hstable : (prefixWord ++ tailWord_1446624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446624).length < 2 ^ (prefixWord ++ tailWord_1446624).sum := by decide
  have hdescent : baseEnd_1446624 < baseStart_1446624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446625 : List Nat := [1, 2, 3, 1, 4, 2, 1, 3, 1, 3, 2]
def baseStart_1446625 : Nat := 118140960795 + 1446625 * 2 ^ 59
def prefixEnd_1446625 : Nat := 4983230072969 + 3 ^ 40 * 1446625 * 2
def baseEnd_1446625 : Nat := 742813951810507806734599

theorem tailTrace_1446625 : CollatzResearch.WordTrace tailWord_1446625 prefixEnd_1446625 742813951810507806734599 := by
  unfold tailWord_1446625
  simp only [CollatzResearch.WordTrace]
  refine ⟨52762748384132163725349329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35175165589421442483566219 52762748384132163725349329)
  ·
    refine ⟨39572061288099122794011997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52762748384132163725349329 39572061288099122794011997)
    ·
      refine ⟨14839522983037171047754499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39572061288099122794011997 14839522983037171047754499)
      ·
        refine ⟨22259284474555756571631749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14839522983037171047754499 22259284474555756571631749)
        ·
          refine ⟨4173615838979204357180953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22259284474555756571631749 4173615838979204357180953)
          ·
            refine ⟨3130211879234403267885715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4173615838979204357180953 3130211879234403267885715)
            ·
              refine ⟨4695317818851604901828573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3130211879234403267885715 4695317818851604901828573)
              ·
                refine ⟨1760744182069351838185715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4695317818851604901828573 1760744182069351838185715)
                ·
                  refine ⟨2641116273104027757278573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1760744182069351838185715 2641116273104027757278573)
                  ·
                    refine ⟨990418602414010408979465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2641116273104027757278573 990418602414010408979465)
                    ·
                      refine ⟨742813951810507806734599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 990418602414010408979465 742813951810507806734599)
                      ·
                        rfl

theorem cell23_1446625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 3, 1, 3, 2].length) (baseStart_1446625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1446625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1446625 prefixEnd_1446625 := by exact prefixLift 1446625
  have htrace : WordTrace (prefixWord ++ tailWord_1446625) baseStart_1446625 baseEnd_1446625 := by
    simpa [prefixWord, tailWord_1446625, baseEnd_1446625] using wordTrace_append hprefix tailTrace_1446625
  have hstable : (prefixWord ++ tailWord_1446625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446625).length < 2 ^ (prefixWord ++ tailWord_1446625).sum := by decide
  have hdescent : baseEnd_1446625 < baseStart_1446625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446632 : List Nat := [2, 1, 4, 1, 4, 2, 1, 2, 2, 1, 3]
def baseStart_1446632 : Nat := 118140960795 + 1446632 * 2 ^ 59
def prefixEnd_1446632 : Nat := 4983230072969 + 3 ^ 40 * 1446632 * 2
def baseEnd_1446632 : Nat := 742817546175089279347067

theorem tailTrace_1446632 : CollatzResearch.WordTrace tailWord_1446632 prefixEnd_1446632 742817546175089279347067 := by
  unfold tailWord_1446632
  simp only [CollatzResearch.WordTrace]
  refine ⟨26381501847553401960427075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35175335796737869280569433 26381501847553401960427075)
  ·
    refine ⟨39572252771330102940640613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26381501847553401960427075 39572252771330102940640613)
    ·
      refine ⟨7419797394624394301370115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39572252771330102940640613 7419797394624394301370115)
      ·
        refine ⟨11129696091936591452055173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7419797394624394301370115 11129696091936591452055173)
        ·
          refine ⟨2086818017238110897260345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11129696091936591452055173 2086818017238110897260345)
          ·
            refine ⟨1565113512928583172945259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2086818017238110897260345 1565113512928583172945259)
            ·
              refine ⟨2347670269392874759417889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1565113512928583172945259 2347670269392874759417889)
              ·
                refine ⟨1760752702044656069563417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2347670269392874759417889 1760752702044656069563417)
                ·
                  refine ⟨1320564526533492052172563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1760752702044656069563417 1320564526533492052172563)
                  ·
                    refine ⟨1980846789800238078258845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1320564526533492052172563 1980846789800238078258845)
                    ·
                      refine ⟨742817546175089279347067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1980846789800238078258845 742817546175089279347067)
                      ·
                        rfl

theorem cell23_1446632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 2, 2, 1, 3].length) (baseStart_1446632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1446632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1446632 prefixEnd_1446632 := by exact prefixLift 1446632
  have htrace : WordTrace (prefixWord ++ tailWord_1446632) baseStart_1446632 baseEnd_1446632 := by
    simpa [prefixWord, tailWord_1446632, baseEnd_1446632] using wordTrace_append hprefix tailTrace_1446632
  have hstable : (prefixWord ++ tailWord_1446632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446632).length < 2 ^ (prefixWord ++ tailWord_1446632).sum := by decide
  have hdescent : baseEnd_1446632 < baseStart_1446632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446711 : List Nat := [1, 1, 3, 1, 2, 1, 3, 2, 4, 1, 4]
def baseStart_1446711 : Nat := 118140960795 + 1446711 * 2 ^ 59
def prefixEnd_1446711 : Nat := 4983230072969 + 3 ^ 40 * 1446711 * 2
def baseEnd_1446711 : Nat := 742858111146794470259203

theorem tailTrace_1446711 : CollatzResearch.WordTrace tailWord_1446711 prefixEnd_1446711 742858111146794470259203 := by
  unfold tailWord_1446711
  simp only [CollatzResearch.WordTrace]
  refine ⟨52765885061820600412979987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35177256707880400275319991 52765885061820600412979987)
  ·
    refine ⟨79148827592730900619469981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52765885061820600412979987 79148827592730900619469981)
    ·
      refine ⟨29680810347274087732301243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79148827592730900619469981 29680810347274087732301243)
      ·
        refine ⟨44521215520911131598451865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29680810347274087732301243 44521215520911131598451865)
        ·
          refine ⟨33390911640683348698838899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44521215520911131598451865 33390911640683348698838899)
          ·
            refine ⟨50086367461025023048258349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33390911640683348698838899 50086367461025023048258349)
            ·
              refine ⟨18782387797884383643096881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50086367461025023048258349 18782387797884383643096881)
              ·
                refine ⟨14086790848413287732322661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18782387797884383643096881 14086790848413287732322661)
                ·
                  refine ⟨2641273284077491449810499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14086790848413287732322661 2641273284077491449810499)
                  ·
                    refine ⟨3961909926116237174715749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2641273284077491449810499 3961909926116237174715749)
                    ·
                      refine ⟨742858111146794470259203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3961909926116237174715749 742858111146794470259203)
                      ·
                        rfl

theorem cell23_1446711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 4, 1, 4].length) (baseStart_1446711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1446711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1446711 prefixEnd_1446711 := by exact prefixLift 1446711
  have htrace : WordTrace (prefixWord ++ tailWord_1446711) baseStart_1446711 baseEnd_1446711 := by
    simpa [prefixWord, tailWord_1446711, baseEnd_1446711] using wordTrace_append hprefix tailTrace_1446711
  have hstable : (prefixWord ++ tailWord_1446711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446711).length < 2 ^ (prefixWord ++ tailWord_1446711).sum := by decide
  have hdescent : baseEnd_1446711 < baseStart_1446711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446728 : List Nat := [2, 1, 3, 1, 1, 3, 4, 1, 2, 1, 4]
def baseStart_1446728 : Nat := 118140960795 + 1446728 * 2 ^ 59
def prefixEnd_1446728 : Nat := 4983230072969 + 3 ^ 40 * 1446728 * 2
def baseEnd_1446728 : Nat := 742866840317920903746625

theorem tailTrace_1446728 : CollatzResearch.WordTrace tailWord_1446728 prefixEnd_1446728 742866840317920903746625 := by
  unfold tailWord_1446728
  simp only [CollatzResearch.WordTrace]
  refine ⟨26383252551379506158174419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35177670068506008210899225 26383252551379506158174419)
  ·
    refine ⟨39574878827069259237261629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26383252551379506158174419 39574878827069259237261629)
    ·
      refine ⟨14840579560150972213973111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39574878827069259237261629 14840579560150972213973111)
      ·
        refine ⟨22260869340226458320959667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14840579560150972213973111 22260869340226458320959667)
        ·
          refine ⟨33391304010339687481439501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22260869340226458320959667 33391304010339687481439501)
          ·
            refine ⟨12521739003877382805539813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33391304010339687481439501 12521739003877382805539813)
            ·
              refine ⟨2347826063227009276038715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12521739003877382805539813 2347826063227009276038715)
              ·
                refine ⟨3521739094840513914058073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2347826063227009276038715 3521739094840513914058073)
                ·
                  refine ⟨2641304321130385435543555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3521739094840513914058073 2641304321130385435543555)
                  ·
                    refine ⟨3961956481695578153315333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2641304321130385435543555 3961956481695578153315333)
                    ·
                      refine ⟨742866840317920903746625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3961956481695578153315333 742866840317920903746625)
                      ·
                        rfl

theorem cell23_1446728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 1, 2, 1, 4].length) (baseStart_1446728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1446728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1446728 prefixEnd_1446728 := by exact prefixLift 1446728
  have htrace : WordTrace (prefixWord ++ tailWord_1446728) baseStart_1446728 baseEnd_1446728 := by
    simpa [prefixWord, tailWord_1446728, baseEnd_1446728] using wordTrace_append hprefix tailTrace_1446728
  have hstable : (prefixWord ++ tailWord_1446728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446728).length < 2 ^ (prefixWord ++ tailWord_1446728).sum := by decide
  have hdescent : baseEnd_1446728 < baseStart_1446728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446741 : List Nat := [1, 3, 2, 2, 2, 1, 2, 1, 2, 1, 6]
def baseStart_1446741 : Nat := 118140960795 + 1446741 * 2 ^ 59
def prefixEnd_1446741 : Nat := 4983230072969 + 3 ^ 40 * 1446741 * 2
def baseEnd_1446741 : Nat := 742873515566429352884065

theorem tailTrace_1446741 : CollatzResearch.WordTrace tailWord_1446741 prefixEnd_1446741 742873515566429352884065 := by
  unfold tailWord_1446741
  simp only [CollatzResearch.WordTrace]
  refine ⟨52766979251711915536572077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35177986167807943691048051 52766979251711915536572077)
  ·
    refine ⟨19787617219391968326214529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52766979251711915536572077 19787617219391968326214529)
    ·
      refine ⟨14840712914543976244660897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19787617219391968326214529 14840712914543976244660897)
      ·
        refine ⟨11130534685907982183495673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14840712914543976244660897 11130534685907982183495673)
        ·
          refine ⟨8347901014430986637621755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11130534685907982183495673 8347901014430986637621755)
          ·
            refine ⟨12521851521646479956432633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8347901014430986637621755 12521851521646479956432633)
            ·
              refine ⟨9391388641234859967324475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12521851521646479956432633 9391388641234859967324475)
              ·
                refine ⟨14087082961852289950986713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9391388641234859967324475 14087082961852289950986713)
                ·
                  refine ⟨10565312221389217463240035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14087082961852289950986713 10565312221389217463240035)
                  ·
                    refine ⟨15847968332083826194860053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10565312221389217463240035 15847968332083826194860053)
                    ·
                      refine ⟨742873515566429352884065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15847968332083826194860053 742873515566429352884065)
                      ·
                        rfl

theorem cell23_1446741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_1446741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1446741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1446741 prefixEnd_1446741 := by exact prefixLift 1446741
  have htrace : WordTrace (prefixWord ++ tailWord_1446741) baseStart_1446741 baseEnd_1446741 := by
    simpa [prefixWord, tailWord_1446741, baseEnd_1446741] using wordTrace_append hprefix tailTrace_1446741
  have hstable : (prefixWord ++ tailWord_1446741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446741).length < 2 ^ (prefixWord ++ tailWord_1446741).sum := by decide
  have hdescent : baseEnd_1446741 < baseStart_1446741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446761 : List Nat := [1, 2, 1, 1, 1, 3, 1, 1, 4, 5, 3]
def baseStart_1446761 : Nat := 118140960795 + 1446761 * 2 ^ 59
def prefixEnd_1446761 : Nat := 4983230072969 + 3 ^ 40 * 1446761 * 2
def baseEnd_1446761 : Nat := 742883785179519274633973

theorem tailTrace_1446761 : CollatzResearch.WordTrace tailWord_1446761 prefixEnd_1446761 742883785179519274633973 := by
  unfold tailWord_1446761
  simp only [CollatzResearch.WordTrace]
  refine ⟨52767708711639458952300137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35178472474426305968200091 52767708711639458952300137)
  ·
    refine ⟨39575781533729594214225103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52767708711639458952300137 39575781533729594214225103)
    ·
      refine ⟨59363672300594391321337655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39575781533729594214225103 59363672300594391321337655)
      ·
        refine ⟨89045508450891586982006483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59363672300594391321337655 89045508450891586982006483)
        ·
          refine ⟨133568262676337380473009725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89045508450891586982006483 133568262676337380473009725)
          ·
            refine ⟨50088098503626517677378647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133568262676337380473009725 50088098503626517677378647)
            ·
              refine ⟨75132147755439776516067971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50088098503626517677378647 75132147755439776516067971)
              ·
                refine ⟨112698221633159664774101957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75132147755439776516067971 112698221633159664774101957)
                ·
                  refine ⟨21130916556217437145144117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 112698221633159664774101957 21130916556217437145144117)
                  ·
                    refine ⟨1981023427145384732357261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21130916556217437145144117 1981023427145384732357261)
                    ·
                      refine ⟨742883785179519274633973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1981023427145384732357261 742883785179519274633973)
                      ·
                        rfl

theorem cell23_1446761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 5, 3].length) (baseStart_1446761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1446761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1446761 prefixEnd_1446761 := by exact prefixLift 1446761
  have htrace : WordTrace (prefixWord ++ tailWord_1446761) baseStart_1446761 baseEnd_1446761 := by
    simpa [prefixWord, tailWord_1446761, baseEnd_1446761] using wordTrace_append hprefix tailTrace_1446761
  have hstable : (prefixWord ++ tailWord_1446761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446761).length < 2 ^ (prefixWord ++ tailWord_1446761).sum := by decide
  have hdescent : baseEnd_1446761 < baseStart_1446761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446782 : List Nat := [4, 2, 3, 1, 2, 1, 1, 1, 1, 4, 3]
def baseStart_1446782 : Nat := 118140960795 + 1446782 * 2 ^ 59
def prefixEnd_1446782 : Nat := 4983230072969 + 3 ^ 40 * 1446782 * 2
def baseEnd_1446782 : Nat := 742894568273263692471377

theorem tailTrace_1446782 : CollatzResearch.WordTrace tailWord_1446782 prefixEnd_1446782 742894568273263692471377 := by
  unfold tailWord_1446782
  simp only [CollatzResearch.WordTrace]
  refine ⟨6596059330570422442351825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35178983096375586359209733 6596059330570422442351825)
  ·
    refine ⟨4947044497927816831763869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6596059330570422442351825 4947044497927816831763869)
    ·
      refine ⟨1855141686722931311911451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4947044497927816831763869 1855141686722931311911451)
      ·
        refine ⟨2782712530084396967867177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1855141686722931311911451 2782712530084396967867177)
        ·
          refine ⟨2087034397563297725900383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2782712530084396967867177 2087034397563297725900383)
          ·
            refine ⟨3130551596344946588850575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2087034397563297725900383 3130551596344946588850575)
            ·
              refine ⟨4695827394517419883275863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3130551596344946588850575 4695827394517419883275863)
              ·
                refine ⟨7043741091776129824913795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4695827394517419883275863 7043741091776129824913795)
                ·
                  refine ⟨10565611637664194737370693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7043741091776129824913795 10565611637664194737370693)
                  ·
                    refine ⟨1981052182062036513257005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10565611637664194737370693 1981052182062036513257005)
                    ·
                      refine ⟨742894568273263692471377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1981052182062036513257005 742894568273263692471377)
                      ·
                        rfl

theorem cell23_1446782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_1446782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1446782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1446782 prefixEnd_1446782 := by exact prefixLift 1446782
  have htrace : WordTrace (prefixWord ++ tailWord_1446782) baseStart_1446782 baseEnd_1446782 := by
    simpa [prefixWord, tailWord_1446782, baseEnd_1446782] using wordTrace_append hprefix tailTrace_1446782
  have hstable : (prefixWord ++ tailWord_1446782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446782).length < 2 ^ (prefixWord ++ tailWord_1446782).sum := by decide
  have hdescent : baseEnd_1446782 < baseStart_1446782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446802 : List Nat := [3, 2, 3, 2, 2, 2, 1, 2, 6]
def baseStart_1446802 : Nat := 118140960795 + 1446802 * 2 ^ 59
def prefixEnd_1446802 : Nat := 4983230072969 + 3 ^ 40 * 1446802 * 2
def baseEnd_1446802 : Nat := 82544981987372623802365

theorem tailTrace_1446802 : CollatzResearch.WordTrace tailWord_1446802 prefixEnd_1446802 82544981987372623802365 := by
  unfold tailWord_1446802
  simp only [CollatzResearch.WordTrace]
  refine ⟨13192301026122730738635665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35179469402993948636361773 13192301026122730738635665)
  ·
    refine ⟨9894225769592048053976749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13192301026122730738635665 9894225769592048053976749)
    ·
      refine ⟨3710334663597018020241281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9894225769592048053976749 3710334663597018020241281)
      ·
        refine ⟨2782750997697763515180961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3710334663597018020241281 2782750997697763515180961)
        ·
          refine ⟨2087063248273322636385721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2782750997697763515180961 2087063248273322636385721)
          ·
            refine ⟨1565297436204991977289291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2087063248273322636385721 1565297436204991977289291)
            ·
              refine ⟨2347946154307487965933937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1565297436204991977289291 2347946154307487965933937)
              ·
                refine ⟨1760959615730615974450453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2347946154307487965933937 1760959615730615974450453)
                ·
                  refine ⟨82544981987372623802365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1760959615730615974450453 82544981987372623802365)
                  ·
                    rfl

theorem cell23_1446802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 2, 6].length) (baseStart_1446802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1446802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1446802 prefixEnd_1446802 := by exact prefixLift 1446802
  have htrace : WordTrace (prefixWord ++ tailWord_1446802) baseStart_1446802 baseEnd_1446802 := by
    simpa [prefixWord, tailWord_1446802, baseEnd_1446802] using wordTrace_append hprefix tailTrace_1446802
  have hstable : (prefixWord ++ tailWord_1446802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446802).length < 2 ^ (prefixWord ++ tailWord_1446802).sum := by decide
  have hdescent : baseEnd_1446802 < baseStart_1446802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446806 : List Nat := [5, 3, 1, 1, 1, 1, 2, 4, 1, 4]
def baseStart_1446806 : Nat := 118140960795 + 1446806 * 2 ^ 59
def prefixEnd_1446806 : Nat := 4983230072969 + 3 ^ 40 * 1446806 * 2
def baseEnd_1446806 : Nat := 247635630602990532857089

theorem tailTrace_1446806 : CollatzResearch.WordTrace tailWord_1446806 prefixEnd_1446806 247635630602990532857089 := by
  unfold tailWord_1446806
  simp only [CollatzResearch.WordTrace]
  refine ⟨3298084374779776977355517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35179566664317621091792181 3298084374779776977355517)
  ·
    refine ⟨1236781640542416366508319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3298084374779776977355517 1236781640542416366508319)
    ·
      refine ⟨1855172460813624549762479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1236781640542416366508319 1855172460813624549762479)
      ·
        refine ⟨2782758691220436824643719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1855172460813624549762479 2782758691220436824643719)
        ·
          refine ⟨4174138036830655236965579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2782758691220436824643719 4174138036830655236965579)
          ·
            refine ⟨6261207055245982855448369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4174138036830655236965579 6261207055245982855448369)
            ·
              refine ⟨4695905291434487141586277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6261207055245982855448369 4695905291434487141586277)
              ·
                refine ⟨880482242143966339047427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4695905291434487141586277 880482242143966339047427)
                ·
                  refine ⟨1320723363215949508571141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 880482242143966339047427 1320723363215949508571141)
                  ·
                    refine ⟨247635630602990532857089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1320723363215949508571141 247635630602990532857089)
                    ·
                      rfl

theorem cell23_1446806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_1446806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1446806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1446806 prefixEnd_1446806 := by exact prefixLift 1446806
  have htrace : WordTrace (prefixWord ++ tailWord_1446806) baseStart_1446806 baseEnd_1446806 := by
    simpa [prefixWord, tailWord_1446806, baseEnd_1446806] using wordTrace_append hprefix tailTrace_1446806
  have hstable : (prefixWord ++ tailWord_1446806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446806).length < 2 ^ (prefixWord ++ tailWord_1446806).sum := by decide
  have hdescent : baseEnd_1446806 < baseStart_1446806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446835 : List Nat := [1, 1, 1, 2, 3, 1, 2, 3, 5, 2, 2]
def baseStart_1446835 : Nat := 118140960795 + 1446835 * 2 ^ 59
def prefixEnd_1446835 : Nat := 4983230072969 + 3 ^ 40 * 1446835 * 2
def baseEnd_1446835 : Nat := 742921782747951985108633

theorem tailTrace_1446835 : CollatzResearch.WordTrace tailWord_1446835 prefixEnd_1446835 742921782747951985108633 := by
  unfold tailWord_1446835
  simp only [CollatzResearch.WordTrace]
  refine ⟨52770407713371369590493959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35180271808914246393662639 52770407713371369590493959)
  ·
    refine ⟨79155611570057054385740939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52770407713371369590493959 79155611570057054385740939)
    ·
      refine ⟨118733417355085581578611409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79155611570057054385740939 118733417355085581578611409)
      ·
        refine ⟨89050063016314186183958557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118733417355085581578611409 89050063016314186183958557)
        ·
          refine ⟨33393773631117819818984459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89050063016314186183958557 33393773631117819818984459)
          ·
            refine ⟨50090660446676729728476689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33393773631117819818984459 50090660446676729728476689)
            ·
              refine ⟨37567995335007547296357517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50090660446676729728476689 37567995335007547296357517)
              ·
                refine ⟨14087998250627830236134069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37567995335007547296357517 14087998250627830236134069)
                ·
                  refine ⟨1320749835996359084637569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14087998250627830236134069 1320749835996359084637569)
                  ·
                    refine ⟨990562376997269313478177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1320749835996359084637569 990562376997269313478177)
                    ·
                      refine ⟨742921782747951985108633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 990562376997269313478177 742921782747951985108633)
                      ·
                        rfl

theorem cell23_1446835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 5, 2, 2].length) (baseStart_1446835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1446835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1446835 prefixEnd_1446835 := by exact prefixLift 1446835
  have htrace : WordTrace (prefixWord ++ tailWord_1446835) baseStart_1446835 baseEnd_1446835 := by
    simpa [prefixWord, tailWord_1446835, baseEnd_1446835] using wordTrace_append hprefix tailTrace_1446835
  have hstable : (prefixWord ++ tailWord_1446835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446835).length < 2 ^ (prefixWord ++ tailWord_1446835).sum := by decide
  have hdescent : baseEnd_1446835 < baseStart_1446835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446855 : List Nat := [1, 1, 4, 1, 1, 2, 4, 3, 1, 2, 3]
def baseStart_1446855 : Nat := 118140960795 + 1446855 * 2 ^ 59
def prefixEnd_1446855 : Nat := 4983230072969 + 3 ^ 40 * 1446855 * 2
def baseEnd_1446855 : Nat := 742932052361041906858541

theorem tailTrace_1446855 : CollatzResearch.WordTrace tailWord_1446855 prefixEnd_1446855 742932052361041906858541 := by
  unfold tailWord_1446855
  simp only [CollatzResearch.WordTrace]
  refine ⟨52771137173298913006222019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35180758115532608670814679 52771137173298913006222019)
  ·
    refine ⟨79156705759948369509333029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52771137173298913006222019 79156705759948369509333029)
    ·
      refine ⟨14841882329990319282999943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79156705759948369509333029 14841882329990319282999943)
      ·
        refine ⟨22262823494985478924499915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14841882329990319282999943 22262823494985478924499915)
        ·
          refine ⟨33394235242478218386749873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22262823494985478924499915 33394235242478218386749873)
          ·
            refine ⟨25045676431858663790062405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33394235242478218386749873 25045676431858663790062405)
            ·
              refine ⟨4696064330973499460636701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25045676431858663790062405 4696064330973499460636701)
              ·
                refine ⟨1761024124115062297738763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4696064330973499460636701 1761024124115062297738763)
                ·
                  refine ⟨2641536186172593446608145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1761024124115062297738763 2641536186172593446608145)
                  ·
                    refine ⟨1981152139629445084956109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2641536186172593446608145 1981152139629445084956109)
                    ·
                      refine ⟨742932052361041906858541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1981152139629445084956109 742932052361041906858541)
                      ·
                        rfl

theorem cell23_1446855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 3, 1, 2, 3].length) (baseStart_1446855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1446855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1446855 prefixEnd_1446855 := by exact prefixLift 1446855
  have htrace : WordTrace (prefixWord ++ tailWord_1446855) baseStart_1446855 baseEnd_1446855 := by
    simpa [prefixWord, tailWord_1446855, baseEnd_1446855] using wordTrace_append hprefix tailTrace_1446855
  have hstable : (prefixWord ++ tailWord_1446855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446855).length < 2 ^ (prefixWord ++ tailWord_1446855).sum := by decide
  have hdescent : baseEnd_1446855 < baseStart_1446855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446879 : List Nat := [1, 1, 2, 3, 5, 2, 2, 1, 2, 4]
def baseStart_1446879 : Nat := 118140960795 + 1446879 * 2 ^ 59
def prefixEnd_1446879 : Nat := 4983230072969 + 3 ^ 40 * 1446879 * 2
def baseEnd_1446879 : Nat := 247648125298916604319477

theorem tailTrace_1446879 : CollatzResearch.WordTrace tailWord_1446879 prefixEnd_1446879 247648125298916604319477 := by
  unfold tailWord_1446879
  simp only [CollatzResearch.WordTrace]
  refine ⟨52772012525211965105095691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35181341683474643403397127 52772012525211965105095691)
  ·
    refine ⟨79158018787817947657643537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52772012525211965105095691 79158018787817947657643537)
    ·
      refine ⟨59368514090863460743232653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79158018787817947657643537 59368514090863460743232653)
      ·
        refine ⟨22263192784073797778712245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59368514090863460743232653 22263192784073797778712245)
        ·
          refine ⟨2087174323506918541754273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22263192784073797778712245 2087174323506918541754273)
          ·
            refine ⟨1565380742630188906315705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2087174323506918541754273 1565380742630188906315705)
            ·
              refine ⟨1174035556972641679736779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1565380742630188906315705 1174035556972641679736779)
              ·
                refine ⟨1761053335458962519605169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1174035556972641679736779 1761053335458962519605169)
                ·
                  refine ⟨1320790001594221889703877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1761053335458962519605169 1320790001594221889703877)
                  ·
                    refine ⟨247648125298916604319477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1320790001594221889703877 247648125298916604319477)
                    ·
                      rfl

theorem cell23_1446879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 2, 1, 2, 4].length) (baseStart_1446879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1446879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1446879 prefixEnd_1446879 := by exact prefixLift 1446879
  have htrace : WordTrace (prefixWord ++ tailWord_1446879) baseStart_1446879 baseEnd_1446879 := by
    simpa [prefixWord, tailWord_1446879, baseEnd_1446879] using wordTrace_append hprefix tailTrace_1446879
  have hstable : (prefixWord ++ tailWord_1446879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446879).length < 2 ^ (prefixWord ++ tailWord_1446879).sum := by decide
  have hdescent : baseEnd_1446879 < baseStart_1446879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446891 : List Nat := [1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 10]
def baseStart_1446891 : Nat := 118140960795 + 1446891 * 2 ^ 59
def prefixEnd_1446891 : Nat := 4983230072969 + 3 ^ 40 * 1446891 * 2
def baseEnd_1446891 : Nat := 742950537664603766008375

theorem tailTrace_1446891 : CollatzResearch.WordTrace tailWord_1446891 prefixEnd_1446891 742950537664603766008375 := by
  unfold tailWord_1446891
  simp only [CollatzResearch.WordTrace]
  refine ⟨52772450201168491154532527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35181633467445660769688351 52772450201168491154532527)
  ·
    refine ⟨79158675301752736731798791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52772450201168491154532527 79158675301752736731798791)
    ·
      refine ⟨118738012952629105097698187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79158675301752736731798791 118738012952629105097698187)
      ·
        refine ⟨178107019428943657646547281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118738012952629105097698187 178107019428943657646547281)
        ·
          refine ⟨133580264571707743234910461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178107019428943657646547281 133580264571707743234910461)
          ·
            refine ⟨50092599214390403713091423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133580264571707743234910461 50092599214390403713091423)
            ·
              refine ⟨75138898821585605569637135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50092599214390403713091423 75138898821585605569637135)
              ·
                refine ⟨112708348232378408354455703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75138898821585605569637135 112708348232378408354455703)
                ·
                  refine ⟨169062522348567612531683555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112708348232378408354455703 169062522348567612531683555)
                  ·
                    refine ⟨253593783522851418797525333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 169062522348567612531683555 253593783522851418797525333)
                    ·
                      refine ⟨742950537664603766008375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 253593783522851418797525333 742950537664603766008375)
                      ·
                        rfl

theorem cell23_1446891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 10].length) (baseStart_1446891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1446891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1446891 prefixEnd_1446891 := by exact prefixLift 1446891
  have htrace : WordTrace (prefixWord ++ tailWord_1446891) baseStart_1446891 baseEnd_1446891 := by
    simpa [prefixWord, tailWord_1446891, baseEnd_1446891] using wordTrace_append hprefix tailTrace_1446891
  have hstable : (prefixWord ++ tailWord_1446891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446891).length < 2 ^ (prefixWord ++ tailWord_1446891).sum := by decide
  have hdescent : baseEnd_1446891 < baseStart_1446891 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446902 : List Nat := [5, 1, 1, 1, 3, 2, 1, 2, 1, 3, 3]
def baseStart_1446902 : Nat := 118140960795 + 1446902 * 2 ^ 59
def prefixEnd_1446902 : Nat := 4983230072969 + 3 ^ 40 * 1446902 * 2
def baseEnd_1446902 : Nat := 742956185951803222970825

theorem tailTrace_1446902 : CollatzResearch.WordTrace tailWord_1446902 prefixEnd_1446902 742956185951803222970825 := by
  unfold tailWord_1446902
  simp only [CollatzResearch.WordTrace]
  refine ⟨3298303212758040002073935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35181900936085760022121973 3298303212758040002073935)
  ·
    refine ⟨4947454819137060003110903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3298303212758040002073935 4947454819137060003110903)
    ·
      refine ⟨7421182228705590004666355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4947454819137060003110903 7421182228705590004666355)
      ·
        refine ⟨11131773343058385006999533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7421182228705590004666355 11131773343058385006999533)
        ·
          refine ⟨4174415003646894377624825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11131773343058385006999533 4174415003646894377624825)
          ·
            refine ⟨3130811252735170783218619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4174415003646894377624825 3130811252735170783218619)
            ·
              refine ⟨4696216879102756174827929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3130811252735170783218619 4696216879102756174827929)
              ·
                refine ⟨3522162659327067131120947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4696216879102756174827929 3522162659327067131120947)
                ·
                  refine ⟨5283243988990600696681421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3522162659327067131120947 5283243988990600696681421)
                  ·
                    refine ⟨1981216495871475261255533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5283243988990600696681421 1981216495871475261255533)
                    ·
                      refine ⟨742956185951803222970825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1981216495871475261255533 742956185951803222970825)
                      ·
                        rfl

theorem cell23_1446902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 2, 1, 3, 3].length) (baseStart_1446902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1446902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1446902 prefixEnd_1446902 := by exact prefixLift 1446902
  have htrace : WordTrace (prefixWord ++ tailWord_1446902) baseStart_1446902 baseEnd_1446902 := by
    simpa [prefixWord, tailWord_1446902, baseEnd_1446902] using wordTrace_append hprefix tailTrace_1446902
  have hstable : (prefixWord ++ tailWord_1446902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446902).length < 2 ^ (prefixWord ++ tailWord_1446902).sum := by decide
  have hdescent : baseEnd_1446902 < baseStart_1446902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446935 : List Nat := [1, 1, 3, 5, 1, 2, 1, 1, 2, 6]
def baseStart_1446935 : Nat := 118140960795 + 1446935 * 2 ^ 59
def prefixEnd_1446935 : Nat := 4983230072969 + 3 ^ 40 * 1446935 * 2
def baseEnd_1446935 : Nat := 247657710271133864619391

theorem tailTrace_1446935 : CollatzResearch.WordTrace tailWord_1446935 prefixEnd_1446935 247657710271133864619391 := by
  unfold tailWord_1446935
  simp only [CollatzResearch.WordTrace]
  refine ⟨52774055013009086669134259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35182703342006057779422839 52774055013009086669134259)
  ·
    refine ⟨79161082519513630003701389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52774055013009086669134259 79161082519513630003701389)
    ·
      refine ⟨29685405944817611251388021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79161082519513630003701389 29685405944817611251388021)
      ·
        refine ⟨2783006807326651054817627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29685405944817611251388021 2783006807326651054817627)
        ·
          refine ⟨4174510210989976582226441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2783006807326651054817627 4174510210989976582226441)
          ·
            refine ⟨3130882658242482436669831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4174510210989976582226441 3130882658242482436669831)
            ·
              refine ⟨4696323987363723655004747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3130882658242482436669831 4696323987363723655004747)
              ·
                refine ⟨7044485981045585482507121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4696323987363723655004747 7044485981045585482507121)
                ·
                  refine ⟨5283364485784189111880341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7044485981045585482507121 5283364485784189111880341)
                  ·
                    refine ⟨247657710271133864619391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5283364485784189111880341 247657710271133864619391)
                    ·
                      rfl

theorem cell23_1446935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 2, 6].length) (baseStart_1446935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1446935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1446935 prefixEnd_1446935 := by exact prefixLift 1446935
  have htrace : WordTrace (prefixWord ++ tailWord_1446935) baseStart_1446935 baseEnd_1446935 := by
    simpa [prefixWord, tailWord_1446935, baseEnd_1446935] using wordTrace_append hprefix tailTrace_1446935
  have hstable : (prefixWord ++ tailWord_1446935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446935).length < 2 ^ (prefixWord ++ tailWord_1446935).sum := by decide
  have hdescent : baseEnd_1446935 < baseStart_1446935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446982 : List Nat := [6, 1, 1, 1, 1, 2, 1, 3, 7]
def baseStart_1446982 : Nat := 118140960795 + 1446982 * 2 ^ 59
def prefixEnd_1446982 : Nat := 4983230072969 + 3 ^ 40 * 1446982 * 2
def baseEnd_1446982 : Nat := 82555251600462545552273

theorem tailTrace_1446982 : CollatzResearch.WordTrace tailWord_1446982 prefixEnd_1446982 82555251600462545552273 := by
  unfold tailWord_1446982
  simp only [CollatzResearch.WordTrace]
  refine ⟨1649242788869962928002975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 35183846162559209130730133 1649242788869962928002975)
  ·
    refine ⟨2473864183304944392004463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1649242788869962928002975 2473864183304944392004463)
    ·
      refine ⟨3710796274957416588006695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2473864183304944392004463 3710796274957416588006695)
      ·
        refine ⟨5566194412436124882010043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3710796274957416588006695 5566194412436124882010043)
        ·
          refine ⟨8349291618654187323015065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5566194412436124882010043 8349291618654187323015065)
          ·
            refine ⟨6261968713990640492261299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8349291618654187323015065 6261968713990640492261299)
            ·
              refine ⟨9392953070985960738391949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6261968713990640492261299 9392953070985960738391949)
              ·
                refine ⟨3522357401619735276896981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9392953070985960738391949 3522357401619735276896981)
                ·
                  refine ⟨82555251600462545552273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3522357401619735276896981 82555251600462545552273)
                  ·
                    rfl

theorem cell23_1446982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_1446982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1446982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1446982 prefixEnd_1446982 := by exact prefixLift 1446982
  have htrace : WordTrace (prefixWord ++ tailWord_1446982) baseStart_1446982 baseEnd_1446982 := by
    simpa [prefixWord, tailWord_1446982, baseEnd_1446982] using wordTrace_append hprefix tailTrace_1446982
  have hstable : (prefixWord ++ tailWord_1446982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446982).length < 2 ^ (prefixWord ++ tailWord_1446982).sum := by decide
  have hdescent : baseEnd_1446982 < baseStart_1446982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446985 : List Nat := [1, 2, 1, 1, 2, 2, 2, 3, 2, 5, 2]
def baseStart_1446985 : Nat := 118140960795 + 1446985 * 2 ^ 59
def prefixEnd_1446985 : Nat := 4983230072969 + 3 ^ 40 * 1446985 * 2
def baseEnd_1446985 : Nat := 742998804846126398232943

theorem tailTrace_1446985 : CollatzResearch.WordTrace tailWord_1446985 prefixEnd_1446985 742998804846126398232943 := by
  unfold tailWord_1446985
  simp only [CollatzResearch.WordTrace]
  refine ⟨52775878662827945208454409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35183919108551963472302939 52775878662827945208454409)
  ·
    refine ⟨39581908997120958906340807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52775878662827945208454409 39581908997120958906340807)
    ·
      refine ⟨59372863495681438359511211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39581908997120958906340807 59372863495681438359511211)
      ·
        refine ⟨89059295243522157539266817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59372863495681438359511211 89059295243522157539266817)
        ·
          refine ⟨66794471432641618154450113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89059295243522157539266817 66794471432641618154450113)
          ·
            refine ⟨50095853574481213615837585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66794471432641618154450113 50095853574481213615837585)
            ·
              refine ⟨37571890180860910211878189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50095853574481213615837585 37571890180860910211878189)
              ·
                refine ⟨14089458817822841329454321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37571890180860910211878189 14089458817822841329454321)
                ·
                  refine ⟨10567094113367130997090741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14089458817822841329454321 10567094113367130997090741)
                  ·
                    refine ⟨990665073128168530977257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10567094113367130997090741 990665073128168530977257)
                    ·
                      refine ⟨742998804846126398232943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 990665073128168530977257 742998804846126398232943)
                      ·
                        rfl

theorem cell23_1446985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 5, 2].length) (baseStart_1446985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1446985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1446985 prefixEnd_1446985 := by exact prefixLift 1446985
  have htrace : WordTrace (prefixWord ++ tailWord_1446985) baseStart_1446985 baseEnd_1446985 := by
    simpa [prefixWord, tailWord_1446985, baseEnd_1446985] using wordTrace_append hprefix tailTrace_1446985
  have hstable : (prefixWord ++ tailWord_1446985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446985).length < 2 ^ (prefixWord ++ tailWord_1446985).sum := by decide
  have hdescent : baseEnd_1446985 < baseStart_1446985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446988 : List Nat := [2, 2, 1, 3, 1, 1, 1, 3, 1, 1, 7]
def baseStart_1446988 : Nat := 118140960795 + 1446988 * 2 ^ 59
def prefixEnd_1446988 : Nat := 4983230072969 + 3 ^ 40 * 1446988 * 2
def baseEnd_1446988 : Nat := 743000345288089886495429

theorem tailTrace_1446988 : CollatzResearch.WordTrace tailWord_1446988 prefixEnd_1446988 743000345288089886495429 := by
  unfold tailWord_1446988
  simp only [CollatzResearch.WordTrace]
  refine ⟨26387994040908538360406809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35183992054544717813875745 26387994040908538360406809)
  ·
    refine ⟨19790995530681403770305107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26387994040908538360406809 19790995530681403770305107)
    ·
      refine ⟨29686493296022105655457661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19790995530681403770305107 29686493296022105655457661)
      ·
        refine ⟨11132434986008289620796623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29686493296022105655457661 11132434986008289620796623)
        ·
          refine ⟨16698652479012434431194935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11132434986008289620796623 16698652479012434431194935)
          ·
            refine ⟨25047978718518651646792403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16698652479012434431194935 25047978718518651646792403)
            ·
              refine ⟨37571968077777977470188605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25047978718518651646792403 37571968077777977470188605)
              ·
                refine ⟨14089488029166741551320727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37571968077777977470188605 14089488029166741551320727)
                ·
                  refine ⟨21134232043750112326981091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14089488029166741551320727 21134232043750112326981091)
                  ·
                    refine ⟨31701348065625168490471637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21134232043750112326981091 31701348065625168490471637)
                    ·
                      refine ⟨743000345288089886495429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 31701348065625168490471637 743000345288089886495429)
                      ·
                        rfl

theorem cell23_1446988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_1446988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1446988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1446988 prefixEnd_1446988 := by exact prefixLift 1446988
  have htrace : WordTrace (prefixWord ++ tailWord_1446988) baseStart_1446988 baseEnd_1446988 := by
    simpa [prefixWord, tailWord_1446988, baseEnd_1446988] using wordTrace_append hprefix tailTrace_1446988
  have hstable : (prefixWord ++ tailWord_1446988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446988).length < 2 ^ (prefixWord ++ tailWord_1446988).sum := by decide
  have hdescent : baseEnd_1446988 < baseStart_1446988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447008 : List Nat := [2, 1, 1, 3, 2, 2, 1, 1, 2, 8]
def baseStart_1447008 : Nat := 118140960795 + 1447008 * 2 ^ 59
def prefixEnd_1447008 : Nat := 4983230072969 + 3 ^ 40 * 1447008 * 2
def baseEnd_1447008 : Nat := 247670204967059936081779

theorem tailTrace_1447008 : CollatzResearch.WordTrace tailWord_1447008 prefixEnd_1447008 247670204967059936081779 := by
  unfold tailWord_1447008
  simp only [CollatzResearch.WordTrace]
  refine ⟨26388358770872310068270839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35184478361163080091027785 26388358770872310068270839)
  ·
    refine ⟨39582538156308465102406259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26388358770872310068270839 39582538156308465102406259)
    ·
      refine ⟨59373807234462697653609389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39582538156308465102406259 59373807234462697653609389)
      ·
        refine ⟨22265177712923511620103521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59373807234462697653609389 22265177712923511620103521)
        ·
          refine ⟨16698883284692633715077641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22265177712923511620103521 16698883284692633715077641)
          ·
            refine ⟨12524162463519475286308231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16698883284692633715077641 12524162463519475286308231)
            ·
              refine ⟨18786243695279212929462347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12524162463519475286308231 18786243695279212929462347)
              ·
                refine ⟨28179365542918819394193521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18786243695279212929462347 28179365542918819394193521)
                ·
                  refine ⟨21134524157189114545645141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28179365542918819394193521 21134524157189114545645141)
                  ·
                    refine ⟨247670204967059936081779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 21134524157189114545645141 247670204967059936081779)
                    ·
                      rfl

theorem cell23_1447008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 2, 8].length) (baseStart_1447008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1447008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1447008 prefixEnd_1447008 := by exact prefixLift 1447008
  have htrace : WordTrace (prefixWord ++ tailWord_1447008) baseStart_1447008 baseEnd_1447008 := by
    simpa [prefixWord, tailWord_1447008, baseEnd_1447008] using wordTrace_append hprefix tailTrace_1447008
  have hstable : (prefixWord ++ tailWord_1447008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447008).length < 2 ^ (prefixWord ++ tailWord_1447008).sum := by decide
  have hdescent : baseEnd_1447008 < baseStart_1447008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447015 : List Nat := [1, 1, 5, 1, 1, 3, 2, 1, 1, 3, 4]
def baseStart_1447015 : Nat := 118140960795 + 1447015 * 2 ^ 59
def prefixEnd_1447015 : Nat := 4983230072969 + 3 ^ 40 * 1447015 * 2
def baseEnd_1447015 : Nat := 743014209265761280857805

theorem tailTrace_1447015 : CollatzResearch.WordTrace tailWord_1447015 prefixEnd_1447015 743014209265761280857805 := by
  unfold tailWord_1447015
  simp only [CollatzResearch.WordTrace]
  refine ⟨52776972852719260332046499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35184648568479506888030999 52776972852719260332046499)
  ·
    refine ⟨79165459279078890498069749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52776972852719260332046499 79165459279078890498069749)
    ·
      refine ⟨7421761807413645984194039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 79165459279078890498069749 7421761807413645984194039)
      ·
        refine ⟨11132642711120468976291059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7421761807413645984194039 11132642711120468976291059)
        ·
          refine ⟨16698964066680703464436589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11132642711120468976291059 16698964066680703464436589)
          ·
            refine ⟨6262111525005263799163721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16698964066680703464436589 6262111525005263799163721)
            ·
              refine ⟨4696583643753947849372791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6262111525005263799163721 4696583643753947849372791)
              ·
                refine ⟨7044875465630921774059187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4696583643753947849372791 7044875465630921774059187)
                ·
                  refine ⟨10567313198446382661088781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7044875465630921774059187 10567313198446382661088781)
                  ·
                    refine ⟨3962742449417393497908293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10567313198446382661088781 3962742449417393497908293)
                    ·
                      refine ⟨743014209265761280857805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3962742449417393497908293 743014209265761280857805)
                      ·
                        rfl

theorem cell23_1447015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_1447015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1447015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1447015 prefixEnd_1447015 := by exact prefixLift 1447015
  have htrace : WordTrace (prefixWord ++ tailWord_1447015) baseStart_1447015 baseEnd_1447015 := by
    simpa [prefixWord, tailWord_1447015, baseEnd_1447015] using wordTrace_append hprefix tailTrace_1447015
  have hstable : (prefixWord ++ tailWord_1447015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447015).length < 2 ^ (prefixWord ++ tailWord_1447015).sum := by decide
  have hdescent : baseEnd_1447015 < baseStart_1447015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447016 : List Nat := [2, 1, 4, 4, 1, 2, 1, 3, 5]
def baseStart_1447016 : Nat := 118140960795 + 1447016 * 2 ^ 59
def prefixEnd_1447016 : Nat := 4983230072969 + 3 ^ 40 * 1447016 * 2
def baseEnd_1447016 : Nat := 82557191416268419660589

theorem tailTrace_1447016 : CollatzResearch.WordTrace tailWord_1447016 prefixEnd_1447016 82557191416268419660589 := by
  unfold tailWord_1447016
  simp only [CollatzResearch.WordTrace]
  refine ⟨26388504662857818751416451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35184672883810425001888601 26388504662857818751416451)
  ·
    refine ⟨39582756994286728127124677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26388504662857818751416451 39582756994286728127124677)
    ·
      refine ⟨7421766936428761523835877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39582756994286728127124677 7421766936428761523835877)
      ·
        refine ⟨1391581300580392785719227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7421766936428761523835877 1391581300580392785719227)
        ·
          refine ⟨2087371950870589178578841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1391581300580392785719227 2087371950870589178578841)
          ·
            refine ⟨1565528963152941883934131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2087371950870589178578841 1565528963152941883934131)
            ·
              refine ⟨2348293444729412825901197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1565528963152941883934131 2348293444729412825901197)
              ·
                refine ⟨880610041773529809712949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2348293444729412825901197 880610041773529809712949)
                ·
                  refine ⟨82557191416268419660589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 880610041773529809712949 82557191416268419660589)
                  ·
                    rfl

theorem cell23_1447016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 3, 5].length) (baseStart_1447016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1447016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1447016 prefixEnd_1447016 := by exact prefixLift 1447016
  have htrace : WordTrace (prefixWord ++ tailWord_1447016) baseStart_1447016 baseEnd_1447016 := by
    simpa [prefixWord, tailWord_1447016, baseEnd_1447016] using wordTrace_append hprefix tailTrace_1447016
  have hstable : (prefixWord ++ tailWord_1447016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447016).length < 2 ^ (prefixWord ++ tailWord_1447016).sum := by decide
  have hdescent : baseEnd_1447016 < baseStart_1447016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447029 : List Nat := [1, 3, 4, 3, 1, 1, 1, 2, 2, 5]
def baseStart_1447029 : Nat := 118140960795 + 1447029 * 2 ^ 59
def prefixEnd_1447029 : Nat := 4983230072969 + 3 ^ 40 * 1447029 * 2
def baseEnd_1447029 : Nat := 247673799331641408694247

theorem tailTrace_1447029 : CollatzResearch.WordTrace tailWord_1447029 prefixEnd_1447029 247673799331641408694247 := by
  unfold tailWord_1447029
  simp only [CollatzResearch.WordTrace]
  refine ⟨52777483474668540723056141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35184988983112360482037427 52777483474668540723056141)
  ·
    refine ⟨19791556303000702771146053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52777483474668540723056141 19791556303000702771146053)
    ·
      refine ⟨3710916806812631769589885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19791556303000702771146053 3710916806812631769589885)
      ·
        refine ⟨1391593802554736913596207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3710916806812631769589885 1391593802554736913596207)
        ·
          refine ⟨2087390703832105370394311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1391593802554736913596207 2087390703832105370394311)
          ·
            refine ⟨3131086055748158055591467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2087390703832105370394311 3131086055748158055591467)
            ·
              refine ⟨4696629083622237083387201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3131086055748158055591467 4696629083622237083387201)
              ·
                refine ⟨3522471812716677812540401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4696629083622237083387201 3522471812716677812540401)
                ·
                  refine ⟨2641853859537508359405301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3522471812716677812540401 2641853859537508359405301)
                  ·
                    refine ⟨247673799331641408694247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2641853859537508359405301 247673799331641408694247)
                    ·
                      rfl

theorem cell23_1447029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_1447029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1447029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1447029 prefixEnd_1447029 := by exact prefixLift 1447029
  have htrace : WordTrace (prefixWord ++ tailWord_1447029) baseStart_1447029 baseEnd_1447029 := by
    simpa [prefixWord, tailWord_1447029, baseEnd_1447029] using wordTrace_append hprefix tailTrace_1447029
  have hstable : (prefixWord ++ tailWord_1447029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447029).length < 2 ^ (prefixWord ++ tailWord_1447029).sum := by decide
  have hdescent : baseEnd_1447029 < baseStart_1447029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447102 : List Nat := [4, 2, 1, 1, 3, 1, 1, 2, 3, 5]
def baseStart_1447102 : Nat := 118140960795 + 1447102 * 2 ^ 59
def prefixEnd_1447102 : Nat := 4983230072969 + 3 ^ 40 * 1447102 * 2
def baseEnd_1447102 : Nat := 247686294027567480156635

theorem tailTrace_1447102 : CollatzResearch.WordTrace tailWord_1447102 prefixEnd_1447102 247686294027567480156635 := by
  unfold tailWord_1447102
  simp only [CollatzResearch.WordTrace]
  refine ⟨6597518250425509273807945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35186764002269382793642373 6597518250425509273807945)
  ·
    refine ⟨4948138687819131955355959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6597518250425509273807945 4948138687819131955355959)
    ·
      refine ⟨7422208031728697933033939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4948138687819131955355959 7422208031728697933033939)
      ·
        refine ⟨11133312047593046899550909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7422208031728697933033939 11133312047593046899550909)
        ·
          refine ⟨4174992017847392587331591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11133312047593046899550909 4174992017847392587331591)
          ·
            refine ⟨6262488026771088880997387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4174992017847392587331591 6262488026771088880997387)
            ·
              refine ⟨9393732040156633321496081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6262488026771088880997387 9393732040156633321496081)
              ·
                refine ⟨7045299030117474991122061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9393732040156633321496081 7045299030117474991122061)
                ·
                  refine ⟨2641987136294053121670773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7045299030117474991122061 2641987136294053121670773)
                  ·
                    refine ⟨247686294027567480156635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2641987136294053121670773 247686294027567480156635)
                    ·
                      rfl

theorem cell23_1447102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 3, 5].length) (baseStart_1447102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1447102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1447102 prefixEnd_1447102 := by exact prefixLift 1447102
  have htrace : WordTrace (prefixWord ++ tailWord_1447102) baseStart_1447102 baseEnd_1447102 := by
    simpa [prefixWord, tailWord_1447102, baseEnd_1447102] using wordTrace_append hprefix tailTrace_1447102
  have hstable : (prefixWord ++ tailWord_1447102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447102).length < 2 ^ (prefixWord ++ tailWord_1447102).sum := by decide
  have hdescent : baseEnd_1447102 < baseStart_1447102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447122 : List Nat := [3, 2, 2, 2, 1, 1, 1, 3, 3, 1, 4]
def baseStart_1447122 : Nat := 118140960795 + 1447122 * 2 ^ 59
def prefixEnd_1447122 : Nat := 4983230072969 + 3 ^ 40 * 1447122 * 2
def baseEnd_1447122 : Nat := 743069151695792362219813

theorem tailTrace_1447122 : CollatzResearch.WordTrace tailWord_1447122 prefixEnd_1447122 743069151695792362219813 := by
  unfold tailWord_1447122
  simp only [CollatzResearch.WordTrace]
  refine ⟨13195218865832904401547905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35187250308887745070794413 13195218865832904401547905)
  ·
    refine ⟨9896414149374678301160929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13195218865832904401547905 9896414149374678301160929)
    ·
      refine ⟨7422310612031008725870697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9896414149374678301160929 7422310612031008725870697)
      ·
        refine ⟨5566732959023256544403023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7422310612031008725870697 5566732959023256544403023)
        ·
          refine ⟨8350099438534884816604535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5566732959023256544403023 8350099438534884816604535)
          ·
            refine ⟨12525149157802327224906803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8350099438534884816604535 12525149157802327224906803)
            ·
              refine ⟨18787723736703490837360205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12525149157802327224906803 18787723736703490837360205)
              ·
                refine ⟨7045396401263809064010077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18787723736703490837360205 7045396401263809064010077)
                ·
                  refine ⟨2642023650473928399003779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7045396401263809064010077 2642023650473928399003779)
                  ·
                    refine ⟨3963035475710892598505669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2642023650473928399003779 3963035475710892598505669)
                    ·
                      refine ⟨743069151695792362219813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3963035475710892598505669 743069151695792362219813)
                      ·
                        rfl

theorem cell23_1447122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_1447122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1447122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1447122 prefixEnd_1447122 := by exact prefixLift 1447122
  have htrace : WordTrace (prefixWord ++ tailWord_1447122) baseStart_1447122 baseEnd_1447122 := by
    simpa [prefixWord, tailWord_1447122, baseEnd_1447122] using wordTrace_append hprefix tailTrace_1447122
  have hstable : (prefixWord ++ tailWord_1447122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447122).length < 2 ^ (prefixWord ++ tailWord_1447122).sum := by decide
  have hdescent : baseEnd_1447122 < baseStart_1447122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447149 : List Nat := [1, 5, 1, 2, 2, 2, 1, 1, 4, 4]
def baseStart_1447149 : Nat := 118140960795 + 1447149 * 2 ^ 59
def prefixEnd_1447149 : Nat := 4983230072969 + 3 ^ 40 * 1447149 * 2
def baseEnd_1447149 : Nat := 247694338557821252194063

theorem tailTrace_1447149 : CollatzResearch.WordTrace tailWord_1447149 prefixEnd_1447149 247694338557821252194063 := by
  unfold tailWord_1447149
  simp only [CollatzResearch.WordTrace]
  refine ⟨52781860234233801217424501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35187906822822534144949667 52781860234233801217424501)
  ·
    refine ⟨4948299396959418864133547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52781860234233801217424501 4948299396959418864133547)
    ·
      refine ⟨7422449095439128296200321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4948299396959418864133547 7422449095439128296200321)
      ·
        refine ⟨5566836821579346222150241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7422449095439128296200321 5566836821579346222150241)
        ·
          refine ⟨4175127616184509666612681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5566836821579346222150241 4175127616184509666612681)
          ·
            refine ⟨3131345712138382249959511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4175127616184509666612681 3131345712138382249959511)
            ·
              refine ⟨4697018568207573374939267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3131345712138382249959511 4697018568207573374939267)
              ·
                refine ⟨7045527852311360062408901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4697018568207573374939267 7045527852311360062408901)
                ·
                  refine ⟨1321036472308380011701669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7045527852311360062408901 1321036472308380011701669)
                  ·
                    refine ⟨247694338557821252194063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1321036472308380011701669 247694338557821252194063)
                    ·
                      rfl

theorem cell23_1447149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 4, 4].length) (baseStart_1447149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1447149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1447149 prefixEnd_1447149 := by exact prefixLift 1447149
  have htrace : WordTrace (prefixWord ++ tailWord_1447149) baseStart_1447149 baseEnd_1447149 := by
    simpa [prefixWord, tailWord_1447149, baseEnd_1447149] using wordTrace_append hprefix tailTrace_1447149
  have hstable : (prefixWord ++ tailWord_1447149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447149).length < 2 ^ (prefixWord ++ tailWord_1447149).sum := by decide
  have hdescent : baseEnd_1447149 < baseStart_1447149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447169 : List Nat := [1, 2, 4, 1, 1, 5, 1, 1, 1, 2, 4]
def baseStart_1447169 : Nat := 118140960795 + 1447169 * 2 ^ 59
def prefixEnd_1447169 : Nat := 4983230072969 + 3 ^ 40 * 1447169 * 2
def baseEnd_1447169 : Nat := 743093285286553678332097

theorem tailTrace_1447169 : CollatzResearch.WordTrace tailWord_1447169 prefixEnd_1447169 743093285286553678332097 := by
  unfold tailWord_1447169
  simp only [CollatzResearch.WordTrace]
  refine ⟨52782589694161344633152561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35188393129440896422101707 52782589694161344633152561)
  ·
    refine ⟨39586942270621008474864421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52782589694161344633152561 39586942270621008474864421)
    ·
      refine ⟨7422551675741439089037079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39586942270621008474864421 7422551675741439089037079)
      ·
        refine ⟨11133827513612158633555619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7422551675741439089037079 11133827513612158633555619)
        ·
          refine ⟨16700741270418237950333429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11133827513612158633555619 16700741270418237950333429)
          ·
            refine ⟨1565694494101709807843759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16700741270418237950333429 1565694494101709807843759)
            ·
              refine ⟨2348541741152564711765639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1565694494101709807843759 2348541741152564711765639)
              ·
                refine ⟨3522812611728847067648459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2348541741152564711765639 3522812611728847067648459)
                ·
                  refine ⟨5284218917593270601472689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3522812611728847067648459 5284218917593270601472689)
                  ·
                    refine ⟨3963164188194952951104517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5284218917593270601472689 3963164188194952951104517)
                    ·
                      refine ⟨743093285286553678332097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3963164188194952951104517 743093285286553678332097)
                      ·
                        rfl

theorem cell23_1447169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 1, 1, 2, 4].length) (baseStart_1447169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1447169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1447169 prefixEnd_1447169 := by exact prefixLift 1447169
  have htrace : WordTrace (prefixWord ++ tailWord_1447169) baseStart_1447169 baseEnd_1447169 := by
    simpa [prefixWord, tailWord_1447169, baseEnd_1447169] using wordTrace_append hprefix tailTrace_1447169
  have hstable : (prefixWord ++ tailWord_1447169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447169).length < 2 ^ (prefixWord ++ tailWord_1447169).sum := by decide
  have hdescent : baseEnd_1447169 < baseStart_1447169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447176 : List Nat := [2, 1, 3, 2, 4, 1, 2, 2, 1, 2, 3]
def baseStart_1447176 : Nat := 118140960795 + 1447176 * 2 ^ 59
def prefixEnd_1447176 : Nat := 4983230072969 + 3 ^ 40 * 1447176 * 2
def baseEnd_1447176 : Nat := 743096879651135150944565

theorem tailTrace_1447176 : CollatzResearch.WordTrace tailWord_1447176 prefixEnd_1447176 743096879651135150944565 := by
  unfold tailWord_1447176
  simp only [CollatzResearch.WordTrace]
  refine ⟨26391422502567992414328691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35188563336757323219104921 26391422502567992414328691)
  ·
    refine ⟨39587133753851988621493037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26391422502567992414328691 39587133753851988621493037)
    ·
      refine ⟨14845175157694495733059889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39587133753851988621493037 14845175157694495733059889)
      ·
        refine ⟨11133881368270871799794917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14845175157694495733059889 11133881368270871799794917)
        ·
          refine ⟨2087602756550788462461547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11133881368270871799794917 2087602756550788462461547)
          ·
            refine ⟨3131404134826182693692321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2087602756550788462461547 3131404134826182693692321)
            ·
              refine ⟨2348553101119637020269241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3131404134826182693692321 2348553101119637020269241)
              ·
                refine ⟨1761414825839727765201931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2348553101119637020269241 1761414825839727765201931)
                ·
                  refine ⟨2642122238759591647802897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1761414825839727765201931 2642122238759591647802897)
                  ·
                    refine ⟨1981591679069693735852173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2642122238759591647802897 1981591679069693735852173)
                    ·
                      refine ⟨743096879651135150944565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1981591679069693735852173 743096879651135150944565)
                      ·
                        rfl

theorem cell23_1447176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 2, 1, 2, 3].length) (baseStart_1447176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1447176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1447176 prefixEnd_1447176 := by exact prefixLift 1447176
  have htrace : WordTrace (prefixWord ++ tailWord_1447176) baseStart_1447176 baseEnd_1447176 := by
    simpa [prefixWord, tailWord_1447176, baseEnd_1447176] using wordTrace_append hprefix tailTrace_1447176
  have hstable : (prefixWord ++ tailWord_1447176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447176).length < 2 ^ (prefixWord ++ tailWord_1447176).sum := by decide
  have hdescent : baseEnd_1447176 < baseStart_1447176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447185 : List Nat := [1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 5]
def baseStart_1447185 : Nat := 118140960795 + 1447185 * 2 ^ 59
def prefixEnd_1447185 : Nat := 4983230072969 + 3 ^ 40 * 1447185 * 2
def baseEnd_1447185 : Nat := 743101500977025615732023

theorem tailTrace_1447185 : CollatzResearch.WordTrace tailWord_1447185 prefixEnd_1447185 743101500977025615732023 := by
  unfold tailWord_1447185
  simp only [CollatzResearch.WordTrace]
  refine ⟨52783173262103379365735009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35188782174735586243823339 52783173262103379365735009)
  ·
    refine ⟨39587379946577534524301257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52783173262103379365735009 39587379946577534524301257)
    ·
      refine ⟨29690534959933150893225943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39587379946577534524301257 29690534959933150893225943)
      ·
        refine ⟨44535802439899726339838915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29690534959933150893225943 44535802439899726339838915)
        ·
          refine ⟨66803703659849589509758373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44535802439899726339838915 66803703659849589509758373)
          ·
            refine ⟨12525694436221798033079695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66803703659849589509758373 12525694436221798033079695)
            ·
              refine ⟨18788541654332697049619543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12525694436221798033079695 18788541654332697049619543)
              ·
                refine ⟨28182812481499045574429315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18788541654332697049619543 28182812481499045574429315)
                ·
                  refine ⟨42274218722248568361643973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28182812481499045574429315 42274218722248568361643973)
                  ·
                    refine ⟨7926416010421606567808245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42274218722248568361643973 7926416010421606567808245)
                    ·
                      refine ⟨743101500977025615732023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7926416010421606567808245 743101500977025615732023)
                      ·
                        rfl

theorem cell23_1447185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 5].length) (baseStart_1447185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1447185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1447185 prefixEnd_1447185 := by exact prefixLift 1447185
  have htrace : WordTrace (prefixWord ++ tailWord_1447185) baseStart_1447185 baseEnd_1447185 := by
    simpa [prefixWord, tailWord_1447185, baseEnd_1447185] using wordTrace_append hprefix tailTrace_1447185
  have hstable : (prefixWord ++ tailWord_1447185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447185).length < 2 ^ (prefixWord ++ tailWord_1447185).sum := by decide
  have hdescent : baseEnd_1447185 < baseStart_1447185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447195 : List Nat := [1, 1, 1, 1, 1, 1, 5, 2, 1, 5, 4]
def baseStart_1447195 : Nat := 118140960795 + 1447195 * 2 ^ 59
def prefixEnd_1447195 : Nat := 4983230072969 + 3 ^ 40 * 1447195 * 2
def baseEnd_1447195 : Nat := 743106635783570576606977

theorem tailTrace_1447195 : CollatzResearch.WordTrace tailWord_1447195 prefixEnd_1447195 743106635783570576606977 := by
  unfold tailWord_1447195
  simp only [CollatzResearch.WordTrace]
  refine ⟨52783537992067151073599039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35189025328044767382399359 52783537992067151073599039)
  ·
    refine ⟨79175306988100726610398559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52783537992067151073599039 79175306988100726610398559)
    ·
      refine ⟨118762960482151089915597839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79175306988100726610398559 118762960482151089915597839)
      ·
        refine ⟨178144440723226634873396759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118762960482151089915597839 178144440723226634873396759)
        ·
          refine ⟨267216661084839952310095139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178144440723226634873396759 267216661084839952310095139)
          ·
            refine ⟨400824991627259928465142709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267216661084839952310095139 400824991627259928465142709)
            ·
              refine ⟨37577342965055618293607129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 400824991627259928465142709 37577342965055618293607129)
              ·
                refine ⟨28183007223791713720205347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37577342965055618293607129 28183007223791713720205347)
                ·
                  refine ⟨42274510835687570580308021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28183007223791713720205347 42274510835687570580308021)
                  ·
                    refine ⟨3963235390845709741903877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42274510835687570580308021 3963235390845709741903877)
                    ·
                      refine ⟨743106635783570576606977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3963235390845709741903877 743106635783570576606977)
                      ·
                        rfl

theorem cell23_1447195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 5, 4].length) (baseStart_1447195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1447195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1447195 prefixEnd_1447195 := by exact prefixLift 1447195
  have htrace : WordTrace (prefixWord ++ tailWord_1447195) baseStart_1447195 baseEnd_1447195 := by
    simpa [prefixWord, tailWord_1447195, baseEnd_1447195] using wordTrace_append hprefix tailTrace_1447195
  have hstable : (prefixWord ++ tailWord_1447195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447195).length < 2 ^ (prefixWord ++ tailWord_1447195).sum := by decide
  have hdescent : baseEnd_1447195 < baseStart_1447195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447215 : List Nat := [1, 1, 2, 1, 2, 1, 3, 1, 3, 3, 5]
def baseStart_1447215 : Nat := 118140960795 + 1447215 * 2 ^ 59
def prefixEnd_1447215 : Nat := 4983230072969 + 3 ^ 40 * 1447215 * 2
def baseEnd_1447215 : Nat := 743116905396660498356885

theorem tailTrace_1447215 : CollatzResearch.WordTrace tailWord_1447215 prefixEnd_1447215 743116905396660498356885 := by
  unfold tailWord_1447215
  simp only [CollatzResearch.WordTrace]
  refine ⟨52784267451994694489327099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35189511634663129659551399 52784267451994694489327099)
  ·
    refine ⟨79176401177992041733990649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52784267451994694489327099 79176401177992041733990649)
    ·
      refine ⟨59382300883494031300492987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79176401177992041733990649 59382300883494031300492987)
      ·
        refine ⟨89073451325241046950739481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59382300883494031300492987 89073451325241046950739481)
        ·
          refine ⟨66805088493930785213054611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89073451325241046950739481 66805088493930785213054611)
          ·
            refine ⟨100207632740896177819581917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66805088493930785213054611 100207632740896177819581917)
            ·
              refine ⟨37577862277836066682343219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100207632740896177819581917 37577862277836066682343219)
              ·
                refine ⟨56366793416754100023514829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37577862277836066682343219 56366793416754100023514829)
                ·
                  refine ⟨21137547531282787508818061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56366793416754100023514829 21137547531282787508818061)
                  ·
                    refine ⟨7926580324231045315806773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21137547531282787508818061 7926580324231045315806773)
                    ·
                      refine ⟨743116905396660498356885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7926580324231045315806773 743116905396660498356885)
                      ·
                        rfl

theorem cell23_1447215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 3, 5].length) (baseStart_1447215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1447215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1447215 prefixEnd_1447215 := by exact prefixLift 1447215
  have htrace : WordTrace (prefixWord ++ tailWord_1447215) baseStart_1447215 baseEnd_1447215 := by
    simpa [prefixWord, tailWord_1447215, baseEnd_1447215] using wordTrace_append hprefix tailTrace_1447215
  have hstable : (prefixWord ++ tailWord_1447215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447215).length < 2 ^ (prefixWord ++ tailWord_1447215).sum := by decide
  have hdescent : baseEnd_1447215 < baseStart_1447215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447233 : List Nat := [1, 2, 5, 2, 1, 1, 3, 2, 1, 3, 2]
def baseStart_1447233 : Nat := 118140960795 + 1447233 * 2 ^ 59
def prefixEnd_1447233 : Nat := 4983230072969 + 3 ^ 40 * 1447233 * 2
def baseEnd_1447233 : Nat := 743126148048441427931803

theorem tailTrace_1447233 : CollatzResearch.WordTrace tailWord_1447233 prefixEnd_1447233 743126148048441427931803 := by
  unfold tailWord_1447233
  simp only [CollatzResearch.WordTrace]
  refine ⟨52784923965929483563482353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35189949310619655708988235 52784923965929483563482353)
  ·
    refine ⟨39588692974447112672611765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52784923965929483563482353 39588692974447112672611765)
    ·
      refine ⟨3711439966354416813057353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39588692974447112672611765 3711439966354416813057353)
      ·
        refine ⟨2783579974765812609793015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3711439966354416813057353 2783579974765812609793015)
        ·
          refine ⟨4175369962148718914689523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2783579974765812609793015 4175369962148718914689523)
          ·
            refine ⟨6263054943223078372034285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4175369962148718914689523 6263054943223078372034285)
            ·
              refine ⟨2348645603708654389512857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6263054943223078372034285 2348645603708654389512857)
              ·
                refine ⟨1761484202781490792134643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2348645603708654389512857 1761484202781490792134643)
                ·
                  refine ⟨2642226304172236188201965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1761484202781490792134643 2642226304172236188201965)
                  ·
                    refine ⟨990834864064588570575737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2642226304172236188201965 990834864064588570575737)
                    ·
                      refine ⟨743126148048441427931803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 990834864064588570575737 743126148048441427931803)
                      ·
                        rfl

theorem cell23_1447233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_1447233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1447233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1447233 prefixEnd_1447233 := by exact prefixLift 1447233
  have htrace : WordTrace (prefixWord ++ tailWord_1447233) baseStart_1447233 baseEnd_1447233 := by
    simpa [prefixWord, tailWord_1447233, baseEnd_1447233] using wordTrace_append hprefix tailTrace_1447233
  have hstable : (prefixWord ++ tailWord_1447233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447233).length < 2 ^ (prefixWord ++ tailWord_1447233).sum := by decide
  have hdescent : baseEnd_1447233 < baseStart_1447233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447235 : List Nat := [1, 1, 1, 3, 1, 3, 1, 3, 9]
def baseStart_1447235 : Nat := 118140960795 + 1447235 * 2 ^ 59
def prefixEnd_1447235 : Nat := 4983230072969 + 3 ^ 40 * 1447235 * 2
def baseEnd_1447235 : Nat := 82569686112194491122977

theorem tailTrace_1447235 : CollatzResearch.WordTrace tailWord_1447235 prefixEnd_1447235 82569686112194491122977 := by
  unfold tailWord_1447235
  simp only [CollatzResearch.WordTrace]
  refine ⟨52784996911922237905055159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35189997941281491936703439 52784996911922237905055159)
  ·
    refine ⟨79177495367883356857582739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52784996911922237905055159 79177495367883356857582739)
    ·
      refine ⟨118766243051825035286374109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79177495367883356857582739 118766243051825035286374109)
      ·
        refine ⟨44537341144434388232390291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118766243051825035286374109 44537341144434388232390291)
        ·
          refine ⟨66806011716651582348585437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44537341144434388232390291 66806011716651582348585437)
          ·
            refine ⟨25052254393744343380719539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66806011716651582348585437 25052254393744343380719539)
            ·
              refine ⟨37578381590616515071079309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25052254393744343380719539 37578381590616515071079309)
              ·
                refine ⟨14091893096481193151654741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37578381590616515071079309 14091893096481193151654741)
                ·
                  refine ⟨82569686112194491122977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 14091893096481193151654741 82569686112194491122977)
                  ·
                    rfl

theorem cell23_1447235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 9].length) (baseStart_1447235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1447235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1447235 prefixEnd_1447235 := by exact prefixLift 1447235
  have htrace : WordTrace (prefixWord ++ tailWord_1447235) baseStart_1447235 baseEnd_1447235 := by
    simpa [prefixWord, tailWord_1447235, baseEnd_1447235] using wordTrace_append hprefix tailTrace_1447235
  have hstable : (prefixWord ++ tailWord_1447235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447235).length < 2 ^ (prefixWord ++ tailWord_1447235).sum := by decide
  have hdescent : baseEnd_1447235 < baseStart_1447235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447269 : List Nat := [1, 3, 1, 3, 1, 2, 3, 4, 5]
def baseStart_1447269 : Nat := 118140960795 + 1447269 * 2 ^ 59
def prefixEnd_1447269 : Nat := 4983230072969 + 3 ^ 40 * 1447269 * 2
def baseEnd_1447269 : Nat := 82571625928000365231293

theorem tailTrace_1447269 : CollatzResearch.WordTrace tailWord_1447269 prefixEnd_1447269 82571625928000365231293 := by
  unfold tailWord_1447269
  simp only [CollatzResearch.WordTrace]
  refine ⟨52786236993799061711792861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35190824662532707807861907 52786236993799061711792861)
  ·
    refine ⟨19794838872674648141922323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52786236993799061711792861 19794838872674648141922323)
    ·
      refine ⟨29692258309011972212883485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19794838872674648141922323 29692258309011972212883485)
      ·
        refine ⟨11134596865879489579831307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29692258309011972212883485 11134596865879489579831307)
        ·
          refine ⟨16701895298819234369746961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11134596865879489579831307 16701895298819234369746961)
          ·
            refine ⟨12526421474114425777310221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16701895298819234369746961 12526421474114425777310221)
            ·
              refine ⟨4697408052792909666491333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12526421474114425777310221 4697408052792909666491333)
              ·
                refine ⟨880764009898670562467125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4697408052792909666491333 880764009898670562467125)
                ·
                  refine ⟨82571625928000365231293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 880764009898670562467125 82571625928000365231293)
                  ·
                    rfl

theorem cell23_1447269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 4, 5].length) (baseStart_1447269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1447269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1447269 prefixEnd_1447269 := by exact prefixLift 1447269
  have htrace : WordTrace (prefixWord ++ tailWord_1447269) baseStart_1447269 baseEnd_1447269 := by
    simpa [prefixWord, tailWord_1447269, baseEnd_1447269] using wordTrace_append hprefix tailTrace_1447269
  have hstable : (prefixWord ++ tailWord_1447269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447269).length < 2 ^ (prefixWord ++ tailWord_1447269).sum := by decide
  have hdescent : baseEnd_1447269 < baseStart_1447269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447282 : List Nat := [3, 2, 1, 2, 1, 2, 2, 2, 1, 7]
def baseStart_1447282 : Nat := 118140960795 + 1447282 * 2 ^ 59
def prefixEnd_1447282 : Nat := 4983230072969 + 3 ^ 40 * 1447282 * 2
def baseEnd_1447282 : Nat := 247717102866837245406359

theorem tailTrace_1447282 : CollatzResearch.WordTrace tailWord_1447282 prefixEnd_1447282 247717102866837245406359 := by
  unfold tailWord_1447282
  simp only [CollatzResearch.WordTrace]
  refine ⟨13196677785687991233004025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35191140761834643288010733 13196677785687991233004025)
  ·
    refine ⟨9897508339265993424753019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13196677785687991233004025 9897508339265993424753019)
    ·
      refine ⟨14846262508898990137129529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9897508339265993424753019 14846262508898990137129529)
      ·
        refine ⟨11134696881674242602847147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14846262508898990137129529 11134696881674242602847147)
        ·
          refine ⟨16702045322511363904270721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11134696881674242602847147 16702045322511363904270721)
          ·
            refine ⟨12526533991883522928203041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16702045322511363904270721 12526533991883522928203041)
            ·
              refine ⟨9394900493912642196152281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12526533991883522928203041 9394900493912642196152281)
              ·
                refine ⟨7046175370434481647114211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9394900493912642196152281 7046175370434481647114211)
                ·
                  refine ⟨10569263055651722470671317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7046175370434481647114211 10569263055651722470671317)
                  ·
                    refine ⟨247717102866837245406359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10569263055651722470671317 247717102866837245406359)
                    ·
                      rfl

theorem cell23_1447282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 1, 7].length) (baseStart_1447282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1447282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1447282 prefixEnd_1447282 := by exact prefixLift 1447282
  have htrace : WordTrace (prefixWord ++ tailWord_1447282) baseStart_1447282 baseEnd_1447282 := by
    simpa [prefixWord, tailWord_1447282, baseEnd_1447282] using wordTrace_append hprefix tailTrace_1447282
  have hstable : (prefixWord ++ tailWord_1447282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447282).length < 2 ^ (prefixWord ++ tailWord_1447282).sum := by decide
  have hdescent : baseEnd_1447282 < baseStart_1447282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447299 : List Nat := [1, 1, 1, 3, 5, 1, 3, 1, 2, 5]
def baseStart_1447299 : Nat := 118140960795 + 1447299 * 2 ^ 59
def prefixEnd_1447299 : Nat := 4983230072969 + 3 ^ 40 * 1447299 * 2
def baseEnd_1447299 : Nat := 247720012590546056568833

theorem tailTrace_1447299 : CollatzResearch.WordTrace tailWord_1447299 prefixEnd_1447299 247720012590546056568833 := by
  unfold tailWord_1447299
  simp only [CollatzResearch.WordTrace]
  refine ⟨52787331183690376835384951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35191554122460251223589967 52787331183690376835384951)
  ·
    refine ⟨79180996775535565253077427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52787331183690376835384951 79180996775535565253077427)
    ·
      refine ⟨118771495163303347879616141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79180996775535565253077427 118771495163303347879616141)
      ·
        refine ⟨44539310686238755454856053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118771495163303347879616141 44539310686238755454856053)
        ·
          refine ⟨4175560376834883323892755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44539310686238755454856053 4175560376834883323892755)
          ·
            refine ⟨6263340565252324985839133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4175560376834883323892755 6263340565252324985839133)
            ·
              refine ⟨2348752711969621869689675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6263340565252324985839133 2348752711969621869689675)
              ·
                refine ⟨3523129067954432804534513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2348752711969621869689675 3523129067954432804534513)
                ·
                  refine ⟨2642346800965824603400885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3523129067954432804534513 2642346800965824603400885)
                  ·
                    refine ⟨247720012590546056568833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2642346800965824603400885 247720012590546056568833)
                    ·
                      rfl

theorem cell23_1447299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 1, 2, 5].length) (baseStart_1447299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1447299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1447299 prefixEnd_1447299 := by exact prefixLift 1447299
  have htrace : WordTrace (prefixWord ++ tailWord_1447299) baseStart_1447299 baseEnd_1447299 := by
    simpa [prefixWord, tailWord_1447299, baseEnd_1447299] using wordTrace_append hprefix tailTrace_1447299
  have hstable : (prefixWord ++ tailWord_1447299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447299).length < 2 ^ (prefixWord ++ tailWord_1447299).sum := by decide
  have hdescent : baseEnd_1447299 < baseStart_1447299 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447314 : List Nat := [3, 2, 3, 3, 2, 1, 1, 2, 2, 2, 2]
def baseStart_1447314 : Nat := 118140960795 + 1447314 * 2 ^ 59
def prefixEnd_1447314 : Nat := 4983230072969 + 3 ^ 40 * 1447314 * 2
def baseEnd_1447314 : Nat := 743167739981455611018931

theorem tailTrace_1447314 : CollatzResearch.WordTrace tailWord_1447314 prefixEnd_1447314 743167739981455611018931 := by
  unfold tailWord_1447314
  simp only [CollatzResearch.WordTrace]
  refine ⟨13196969569659008599295249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35191918852424022931453997 13196969569659008599295249)
  ·
    refine ⟨9897727177244256449471437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13196969569659008599295249 9897727177244256449471437)
    ·
      refine ⟨3711647691466596168551789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9897727177244256449471437 3711647691466596168551789)
      ·
        refine ⟨1391867884299973563206921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3711647691466596168551789 1391867884299973563206921)
        ·
          refine ⟨1043900913224980172405191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1391867884299973563206921 1043900913224980172405191)
          ·
            refine ⟨1565851369837470258607787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1043900913224980172405191 1565851369837470258607787)
            ·
              refine ⟨2348777054756205387911681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1565851369837470258607787 2348777054756205387911681)
              ·
                refine ⟨1761582791067154040933761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2348777054756205387911681 1761582791067154040933761)
                ·
                  refine ⟨1321187093300365530700321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1761582791067154040933761 1321187093300365530700321)
                  ·
                    refine ⟨990890319975274148025241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1321187093300365530700321 990890319975274148025241)
                    ·
                      refine ⟨743167739981455611018931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 990890319975274148025241 743167739981455611018931)
                      ·
                        rfl

theorem cell23_1447314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_1447314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1447314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1447314 prefixEnd_1447314 := by exact prefixLift 1447314
  have htrace : WordTrace (prefixWord ++ tailWord_1447314) baseStart_1447314 baseEnd_1447314 := by
    simpa [prefixWord, tailWord_1447314, baseEnd_1447314] using wordTrace_append hprefix tailTrace_1447314
  have hstable : (prefixWord ++ tailWord_1447314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447314).length < 2 ^ (prefixWord ++ tailWord_1447314).sum := by decide
  have hdescent : baseEnd_1447314 < baseStart_1447314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447332 : List Nat := [2, 3, 1, 2, 1, 1, 1, 1, 4, 1, 6]
def baseStart_1447332 : Nat := 118140960795 + 1447332 * 2 ^ 59
def prefixEnd_1447332 : Nat := 4983230072969 + 3 ^ 40 * 1447332 * 2
def baseEnd_1447332 : Nat := 743176982633236540593847

theorem tailTrace_1447332 : CollatzResearch.WordTrace tailWord_1447332 prefixEnd_1447332 743176982633236540593847 := by
  unfold tailWord_1447332
  simp only [CollatzResearch.WordTrace]
  refine ⟨26394267396285411735668125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35192356528380548980890833 26394267396285411735668125)
  ·
    refine ⟨9897850273607029400875547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26394267396285411735668125 9897850273607029400875547)
    ·
      refine ⟨14846775410410544101313321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9897850273607029400875547 14846775410410544101313321)
      ·
        refine ⟨11135081557807908075984991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14846775410410544101313321 11135081557807908075984991)
        ·
          refine ⟨16702622336711862113977487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11135081557807908075984991 16702622336711862113977487)
          ·
            refine ⟨25053933505067793170966231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16702622336711862113977487 25053933505067793170966231)
            ·
              refine ⟨37580900257601689756449347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25053933505067793170966231 37580900257601689756449347)
              ·
                refine ⟨56371350386402534634674021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37580900257601689756449347 56371350386402534634674021)
                ·
                  refine ⟨10569628197450475244001379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56371350386402534634674021 10569628197450475244001379)
                  ·
                    refine ⟨15854442296175712866002069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10569628197450475244001379 15854442296175712866002069)
                    ·
                      refine ⟨743176982633236540593847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15854442296175712866002069 743176982633236540593847)
                      ·
                        rfl

theorem cell23_1447332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_1447332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1447332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1447332 prefixEnd_1447332 := by exact prefixLift 1447332
  have htrace : WordTrace (prefixWord ++ tailWord_1447332) baseStart_1447332 baseEnd_1447332 := by
    simpa [prefixWord, tailWord_1447332, baseEnd_1447332] using wordTrace_append hprefix tailTrace_1447332
  have hstable : (prefixWord ++ tailWord_1447332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447332).length < 2 ^ (prefixWord ++ tailWord_1447332).sum := by decide
  have hdescent : baseEnd_1447332 < baseStart_1447332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447380 : List Nat := [2, 4, 1, 2, 4, 1, 1, 1, 3, 4]
def baseStart_1447380 : Nat := 118140960795 + 1447380 * 2 ^ 59
def prefixEnd_1447380 : Nat := 4983230072969 + 3 ^ 40 * 1447380 * 2
def baseEnd_1447380 : Nat := 247733876568217450931209

theorem tailTrace_1447380 : CollatzResearch.WordTrace tailWord_1447380 prefixEnd_1447380 247733876568217450931209 := by
  unfold tailWord_1447380
  simp only [CollatzResearch.WordTrace]
  refine ⟨26395142748198463834541797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35193523664264618446055729 26395142748198463834541797)
  ·
    refine ⟨4949089265287211968976587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26395142748198463834541797 4949089265287211968976587)
    ·
      refine ⟨7423633897930817953464881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4949089265287211968976587 7423633897930817953464881)
      ·
        refine ⟨5567725423448113465098661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7423633897930817953464881 5567725423448113465098661)
        ·
          refine ⟨1043948516896521274705999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5567725423448113465098661 1043948516896521274705999)
          ·
            refine ⟨1565922775344781912058999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1043948516896521274705999 1565922775344781912058999)
            ·
              refine ⟨2348884163017172868088499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1565922775344781912058999 2348884163017172868088499)
              ·
                refine ⟨3523326244525759302132749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2348884163017172868088499 3523326244525759302132749)
                ·
                  refine ⟨1321247341697159738299781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3523326244525759302132749 1321247341697159738299781)
                  ·
                    refine ⟨247733876568217450931209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1321247341697159738299781 247733876568217450931209)
                    ·
                      rfl

theorem cell23_1447380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 1, 3, 4].length) (baseStart_1447380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1447380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1447380 prefixEnd_1447380 := by exact prefixLift 1447380
  have htrace : WordTrace (prefixWord ++ tailWord_1447380) baseStart_1447380 baseEnd_1447380 := by
    simpa [prefixWord, tailWord_1447380, baseEnd_1447380] using wordTrace_append hprefix tailTrace_1447380
  have hstable : (prefixWord ++ tailWord_1447380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447380).length < 2 ^ (prefixWord ++ tailWord_1447380).sum := by decide
  have hdescent : baseEnd_1447380 < baseStart_1447380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447454 : List Nat := [4, 3, 3, 1, 1, 1, 1, 2, 3, 1, 3]
def baseStart_1447454 : Nat := 118140960795 + 1447454 * 2 ^ 59
def prefixEnd_1447454 : Nat := 4983230072969 + 3 ^ 40 * 1447454 * 2
def baseEnd_1447454 : Nat := 743239627273085063268287

theorem tailTrace_1447454 : CollatzResearch.WordTrace tailWord_1447454 prefixEnd_1447454 743239627273085063268287 := by
  unfold tailWord_1447454
  simp only [CollatzResearch.WordTrace]
  refine ⟨6599123062266104788409677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35195322998752558871518277 6599123062266104788409677)
  ·
    refine ⟨2474671148349789295653629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6599123062266104788409677 2474671148349789295653629)
    ·
      refine ⟨928001680631170985870111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2474671148349789295653629 928001680631170985870111)
      ·
        refine ⟨1392002520946756478805167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 928001680631170985870111 1392002520946756478805167)
        ·
          refine ⟨2088003781420134718207751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1392002520946756478805167 2088003781420134718207751)
          ·
            refine ⟨3132005672130202077311627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2088003781420134718207751 3132005672130202077311627)
            ·
              refine ⟨4698008508195303115967441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3132005672130202077311627 4698008508195303115967441)
              ·
                refine ⟨3523506381146477336975581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4698008508195303115967441 3523506381146477336975581)
                ·
                  refine ⟨1321314892929929001365843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3523506381146477336975581 1321314892929929001365843)
                  ·
                    refine ⟨1981972339394893502048765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1321314892929929001365843 1981972339394893502048765)
                    ·
                      refine ⟨743239627273085063268287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1981972339394893502048765 743239627273085063268287)
                      ·
                        rfl

theorem cell23_1447454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_1447454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1447454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1447454 prefixEnd_1447454 := by exact prefixLift 1447454
  have htrace : WordTrace (prefixWord ++ tailWord_1447454) baseStart_1447454 baseEnd_1447454 := by
    simpa [prefixWord, tailWord_1447454, baseEnd_1447454] using wordTrace_append hprefix tailTrace_1447454
  have hstable : (prefixWord ++ tailWord_1447454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447454).length < 2 ^ (prefixWord ++ tailWord_1447454).sum := by decide
  have hdescent : baseEnd_1447454 < baseStart_1447454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447456 : List Nat := [2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 4]
def baseStart_1447456 : Nat := 118140960795 + 1447456 * 2 ^ 59
def prefixEnd_1447456 : Nat := 4983230072969 + 3 ^ 40 * 1447456 * 2
def baseEnd_1447456 : Nat := 743240654234394055443277

theorem tailTrace_1447456 : CollatzResearch.WordTrace tailWord_1447456 prefixEnd_1447456 743240654234394055443277 := by
  unfold tailWord_1447456
  simp only [CollatzResearch.WordTrace]
  refine ⟨26396528722060796324425111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35195371629414395099233481 26396528722060796324425111)
  ·
    refine ⟨39594793083091194486637667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26396528722060796324425111 39594793083091194486637667)
    ·
      refine ⟨59392189624636791729956501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39594793083091194486637667 59392189624636791729956501)
      ·
        refine ⟨2784008888654849612341711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 59392189624636791729956501 2784008888654849612341711)
        ·
          refine ⟨4176013332982274418512567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2784008888654849612341711 4176013332982274418512567)
          ·
            refine ⟨6264019999473411627768851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4176013332982274418512567 6264019999473411627768851)
            ·
              refine ⟨9396029999210117441653277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6264019999473411627768851 9396029999210117441653277)
              ·
                refine ⟨3523511249703794040619979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9396029999210117441653277 3523511249703794040619979)
                ·
                  refine ⟨5285266874555691060929969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3523511249703794040619979 5285266874555691060929969)
                  ·
                    refine ⟨3963950155916768295697477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5285266874555691060929969 3963950155916768295697477)
                    ·
                      refine ⟨743240654234394055443277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3963950155916768295697477 743240654234394055443277)
                      ·
                        rfl

theorem cell23_1447456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_1447456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1447456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1447456 prefixEnd_1447456 := by exact prefixLift 1447456
  have htrace : WordTrace (prefixWord ++ tailWord_1447456) baseStart_1447456 baseEnd_1447456 := by
    simpa [prefixWord, tailWord_1447456, baseEnd_1447456] using wordTrace_append hprefix tailTrace_1447456
  have hstable : (prefixWord ++ tailWord_1447456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447456).length < 2 ^ (prefixWord ++ tailWord_1447456).sum := by decide
  have hdescent : baseEnd_1447456 < baseStart_1447456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447466 : List Nat := [3, 1, 4, 1, 1, 1, 5, 7]
def baseStart_1447466 : Nat := 118140960795 + 1447466 * 2 ^ 59
def prefixEnd_1447466 : Nat := 4983230072969 + 3 ^ 40 * 1447466 * 2
def baseEnd_1447466 : Nat := 27527621816331074678453

theorem tailTrace_1447466 : CollatzResearch.WordTrace tailWord_1447466 prefixEnd_1447466 27527621816331074678453 := by
  unfold tailWord_1447466
  simp only [CollatzResearch.WordTrace]
  refine ⟨13198355543521341089178563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35195614782723576237809501 13198355543521341089178563)
  ·
    refine ⟨19797533315282011633767845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13198355543521341089178563 19797533315282011633767845)
    ·
      refine ⟨3712037496615377181331471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19797533315282011633767845 3712037496615377181331471)
      ·
        refine ⟨5568056244923065771997207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3712037496615377181331471 5568056244923065771997207)
        ·
          refine ⟨8352084367384598657995811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5568056244923065771997207 8352084367384598657995811)
          ·
            refine ⟨12528126551076897986993717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8352084367384598657995811 12528126551076897986993717)
            ·
              refine ⟨1174511864163459186280661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12528126551076897986993717 1174511864163459186280661)
              ·
                refine ⟨27527621816331074678453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1174511864163459186280661 27527621816331074678453)
                ·
                  rfl

theorem cell23_1447466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 5, 7].length) (baseStart_1447466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1447466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1447466 prefixEnd_1447466 := by exact prefixLift 1447466
  have htrace : WordTrace (prefixWord ++ tailWord_1447466) baseStart_1447466 baseEnd_1447466 := by
    simpa [prefixWord, tailWord_1447466, baseEnd_1447466] using wordTrace_append hprefix tailTrace_1447466
  have hstable : (prefixWord ++ tailWord_1447466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447466).length < 2 ^ (prefixWord ++ tailWord_1447466).sum := by decide
  have hdescent : baseEnd_1447466 < baseStart_1447466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447477 : List Nat := [1, 3, 3, 1, 1, 4, 2, 3, 1, 2, 2]
def baseStart_1447477 : Nat := 118140960795 + 1447477 * 2 ^ 59
def prefixEnd_1447477 : Nat := 4983230072969 + 3 ^ 40 * 1447477 * 2
def baseEnd_1447477 : Nat := 743251437328138473280681

theorem tailTrace_1447477 : CollatzResearch.WordTrace tailWord_1447477 prefixEnd_1447477 743251437328138473280681 := by
  unfold tailWord_1447477
  simp only [CollatzResearch.WordTrace]
  refine ⟨52793823377045513235364685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35195882251363675490243123 52793823377045513235364685)
  ·
    refine ⟨19797683766392067463261757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52793823377045513235364685 19797683766392067463261757)
    ·
      refine ⟨7424131412397025298723159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19797683766392067463261757 7424131412397025298723159)
      ·
        refine ⟨11136197118595537948084739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7424131412397025298723159 11136197118595537948084739)
        ·
          refine ⟨16704295677893306922127109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11136197118595537948084739 16704295677893306922127109)
          ·
            refine ⟨3132055439604995047898833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16704295677893306922127109 3132055439604995047898833)
            ·
              refine ⟨2349041579703746285924125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3132055439604995047898833 2349041579703746285924125)
              ·
                refine ⟨880890592388904857221547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2349041579703746285924125 880890592388904857221547)
                ·
                  refine ⟨1321335888583357285832321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 880890592388904857221547 1321335888583357285832321)
                  ·
                    refine ⟨991001916437517964374241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1321335888583357285832321 991001916437517964374241)
                    ·
                      refine ⟨743251437328138473280681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 991001916437517964374241 743251437328138473280681)
                      ·
                        rfl

theorem cell23_1447477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 3, 1, 2, 2].length) (baseStart_1447477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1447477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1447477 prefixEnd_1447477 := by exact prefixLift 1447477
  have htrace : WordTrace (prefixWord ++ tailWord_1447477) baseStart_1447477 baseEnd_1447477 := by
    simpa [prefixWord, tailWord_1447477, baseEnd_1447477] using wordTrace_append hprefix tailTrace_1447477
  have hstable : (prefixWord ++ tailWord_1447477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447477).length < 2 ^ (prefixWord ++ tailWord_1447477).sum := by decide
  have hdescent : baseEnd_1447477 < baseStart_1447477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447480 : List Nat := [2, 1, 2, 1, 4, 4, 2, 1, 1, 2, 3]
def baseStart_1447480 : Nat := 118140960795 + 1447480 * 2 ^ 59
def prefixEnd_1447480 : Nat := 4983230072969 + 3 ^ 40 * 1447480 * 2
def baseEnd_1447480 : Nat := 743252977770101961543167

theorem tailTrace_1447480 : CollatzResearch.WordTrace tailWord_1447480 prefixEnd_1447480 743252977770101961543167 := by
  unfold tailWord_1447480
  simp only [CollatzResearch.WordTrace]
  refine ⟨26396966398017322373861947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35195955197356429831815929 26396966398017322373861947)
  ·
    refine ⟨39595449597025983560792921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26396966398017322373861947 39595449597025983560792921)
    ·
      refine ⟨29696587197769487670594691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39595449597025983560792921 29696587197769487670594691)
      ·
        refine ⟨44544880796654231505892037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29696587197769487670594691 44544880796654231505892037)
        ·
          refine ⟨8352165149372668407354757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44544880796654231505892037 8352165149372668407354757)
          ·
            refine ⟨1566030965507375326379017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8352165149372668407354757 1566030965507375326379017)
            ·
              refine ⟨1174523224130531494784263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1566030965507375326379017 1174523224130531494784263)
              ·
                refine ⟨1761784836195797242176395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1174523224130531494784263 1761784836195797242176395)
                ·
                  refine ⟨2642677254293695863264593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1761784836195797242176395 2642677254293695863264593)
                  ·
                    refine ⟨1982007940720271897448445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2642677254293695863264593 1982007940720271897448445)
                    ·
                      refine ⟨743252977770101961543167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1982007940720271897448445 743252977770101961543167)
                      ·
                        rfl

theorem cell23_1447480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 2, 1, 1, 2, 3].length) (baseStart_1447480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1447480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1447480 prefixEnd_1447480 := by exact prefixLift 1447480
  have htrace : WordTrace (prefixWord ++ tailWord_1447480) baseStart_1447480 baseEnd_1447480 := by
    simpa [prefixWord, tailWord_1447480, baseEnd_1447480] using wordTrace_append hprefix tailTrace_1447480
  have hstable : (prefixWord ++ tailWord_1447480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447480).length < 2 ^ (prefixWord ++ tailWord_1447480).sum := by decide
  have hdescent : baseEnd_1447480 < baseStart_1447480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447494 : List Nat := [6, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2]
def baseStart_1447494 : Nat := 118140960795 + 1447494 * 2 ^ 59
def prefixEnd_1447494 : Nat := 4983230072969 + 3 ^ 40 * 1447494 * 2
def baseEnd_1447494 : Nat := 743260166499264906768103

theorem tailTrace_1447494 : CollatzResearch.WordTrace tailWord_1447494 prefixEnd_1447494 743260166499264906768103 := by
  unfold tailWord_1447494
  simp only [CollatzResearch.WordTrace]
  refine ⟨1649826356811997660585423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 35196295611989283425822357 1649826356811997660585423)
  ·
    refine ⟨2474739535217996490878135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1649826356811997660585423 2474739535217996490878135)
    ·
      refine ⟨3712109302826994736317203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2474739535217996490878135 3712109302826994736317203)
      ·
        refine ⟨5568163954240492104475805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3712109302826994736317203 5568163954240492104475805)
        ·
          refine ⟨2088061482840184539178427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5568163954240492104475805 2088061482840184539178427)
          ·
            refine ⟨3132092224260276808767641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2088061482840184539178427 3132092224260276808767641)
            ·
              refine ⟨2349069168195207606575731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3132092224260276808767641 2349069168195207606575731)
              ·
                refine ⟨3523603752292811409863597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2349069168195207606575731 3523603752292811409863597)
                ·
                  refine ⟨1321351407109804278698849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3523603752292811409863597 1321351407109804278698849)
                  ·
                    refine ⟨991013555332353209024137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1321351407109804278698849 991013555332353209024137)
                    ·
                      refine ⟨743260166499264906768103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 991013555332353209024137 743260166499264906768103)
                      ·
                        rfl

theorem cell23_1447494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2].length) (baseStart_1447494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1447494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1447494 prefixEnd_1447494 := by exact prefixLift 1447494
  have htrace : WordTrace (prefixWord ++ tailWord_1447494) baseStart_1447494 baseEnd_1447494 := by
    simpa [prefixWord, tailWord_1447494, baseEnd_1447494] using wordTrace_append hprefix tailTrace_1447494
  have hstable : (prefixWord ++ tailWord_1447494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447494).length < 2 ^ (prefixWord ++ tailWord_1447494).sum := by decide
  have hdescent : baseEnd_1447494 < baseStart_1447494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447517 : List Nat := [1, 4, 4, 2, 2, 1, 2, 7]
def baseStart_1447517 : Nat := 118140960795 + 1447517 * 2 ^ 59
def prefixEnd_1447517 : Nat := 4983230072969 + 3 ^ 40 * 1447517 * 2
def baseEnd_1447517 : Nat := 27528591724234011732611

theorem tailTrace_1447517 : CollatzResearch.WordTrace tailWord_1447517 prefixEnd_1447517 27528591724234011732611 := by
  unfold tailWord_1447517
  simp only [CollatzResearch.WordTrace]
  refine ⟨52795282296900600066820805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35196854864600400044547203 52795282296900600066820805)
  ·
    refine ⟨9899115430668862512528901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52795282296900600066820805 9899115430668862512528901)
    ·
      refine ⟨1856084143250411721099169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9899115430668862512528901 1856084143250411721099169)
      ·
        refine ⟨1392063107437808790824377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1856084143250411721099169 1392063107437808790824377)
        ·
          refine ⟨1044047330578356593118283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1392063107437808790824377 1044047330578356593118283)
          ·
            refine ⟨1566070995867534889677425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1044047330578356593118283 1566070995867534889677425)
            ·
              refine ⟨1174553246900651167258069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1566070995867534889677425 1174553246900651167258069)
              ·
                refine ⟨27528591724234011732611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1174553246900651167258069 27528591724234011732611)
                ·
                  rfl

theorem cell23_1447517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 2, 7].length) (baseStart_1447517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1447517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1447517 prefixEnd_1447517 := by exact prefixLift 1447517
  have htrace : WordTrace (prefixWord ++ tailWord_1447517) baseStart_1447517 baseEnd_1447517 := by
    simpa [prefixWord, tailWord_1447517, baseEnd_1447517] using wordTrace_append hprefix tailTrace_1447517
  have hstable : (prefixWord ++ tailWord_1447517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447517).length < 2 ^ (prefixWord ++ tailWord_1447517).sum := by decide
  have hdescent : baseEnd_1447517 < baseStart_1447517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447529 : List Nat := [1, 2, 1, 1, 1, 4, 2, 2, 1, 4, 4]
def baseStart_1447529 : Nat := 118140960795 + 1447529 * 2 ^ 59
def prefixEnd_1447529 : Nat := 4983230072969 + 3 ^ 40 * 1447529 * 2
def baseEnd_1447529 : Nat := 743278138322172269830441

theorem tailTrace_1447529 : CollatzResearch.WordTrace tailWord_1447529 prefixEnd_1447529 743278138322172269830441 := by
  unfold tailWord_1447529
  simp only [CollatzResearch.WordTrace]
  refine ⟨52795719972857126116257641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35197146648571417410838427 52795719972857126116257641)
  ·
    refine ⟨39596789979642844587193231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52795719972857126116257641 39596789979642844587193231)
    ·
      refine ⟨59395184969464266880789847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39596789979642844587193231 59395184969464266880789847)
      ·
        refine ⟨89092777454196400321184771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59395184969464266880789847 89092777454196400321184771)
        ·
          refine ⟨133639166181294600481777157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89092777454196400321184771 133639166181294600481777157)
          ·
            refine ⟨25057343658992737590333217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 133639166181294600481777157 25057343658992737590333217)
            ·
              refine ⟨18793007744244553192749913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25057343658992737590333217 18793007744244553192749913)
              ·
                refine ⟨14094755808183414894562435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18793007744244553192749913 14094755808183414894562435)
                ·
                  refine ⟨21142133712275122341843653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14094755808183414894562435 21142133712275122341843653)
                  ·
                    refine ⟨3964150071051585439095685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21142133712275122341843653 3964150071051585439095685)
                    ·
                      refine ⟨743278138322172269830441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3964150071051585439095685 743278138322172269830441)
                      ·
                        rfl

theorem cell23_1447529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 4, 4].length) (baseStart_1447529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1447529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1447529 prefixEnd_1447529 := by exact prefixLift 1447529
  have htrace : WordTrace (prefixWord ++ tailWord_1447529) baseStart_1447529 baseEnd_1447529 := by
    simpa [prefixWord, tailWord_1447529, baseEnd_1447529] using wordTrace_append hprefix tailTrace_1447529
  have hstable : (prefixWord ++ tailWord_1447529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447529).length < 2 ^ (prefixWord ++ tailWord_1447529).sum := by decide
  have hdescent : baseEnd_1447529 < baseStart_1447529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447536 : List Nat := [2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 5]
def baseStart_1447536 : Nat := 118140960795 + 1447536 * 2 ^ 59
def prefixEnd_1447536 : Nat := 4983230072969 + 3 ^ 40 * 1447536 * 2
def baseEnd_1447536 : Nat := 743281732686753742442909

theorem tailTrace_1447536 : CollatzResearch.WordTrace tailWord_1447536 prefixEnd_1447536 743281732686753742442909 := by
  unfold tailWord_1447536
  simp only [CollatzResearch.WordTrace]
  refine ⟨26397987641915883155881231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35197316855887844207841641 26397987641915883155881231)
  ·
    refine ⟨39596981462873824733821847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26397987641915883155881231 39596981462873824733821847)
    ·
      refine ⟨59395472194310737100732771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39596981462873824733821847 59395472194310737100732771)
      ·
        refine ⟨89093208291466105651099157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59395472194310737100732771 89093208291466105651099157)
        ·
          refine ⟨4176244138662473702395273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 89093208291466105651099157 4176244138662473702395273)
          ·
            refine ⟨3132183103996855276796455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4176244138662473702395273 3132183103996855276796455)
            ·
              refine ⟨4698274655995282915194683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3132183103996855276796455 4698274655995282915194683)
              ·
                refine ⟨7047411983992924372792025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4698274655995282915194683 7047411983992924372792025)
                ·
                  refine ⟨5285558987994693279594019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7047411983992924372792025 5285558987994693279594019)
                  ·
                    refine ⟨7928338481992039919391029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5285558987994693279594019 7928338481992039919391029)
                    ·
                      refine ⟨743281732686753742442909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7928338481992039919391029 743281732686753742442909)
                      ·
                        rfl

theorem cell23_1447536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 5].length) (baseStart_1447536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1447536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1447536 prefixEnd_1447536 := by exact prefixLift 1447536
  have htrace : WordTrace (prefixWord ++ tailWord_1447536) baseStart_1447536 baseEnd_1447536 := by
    simpa [prefixWord, tailWord_1447536, baseEnd_1447536] using wordTrace_append hprefix tailTrace_1447536
  have hstable : (prefixWord ++ tailWord_1447536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447536).length < 2 ^ (prefixWord ++ tailWord_1447536).sum := by decide
  have hdescent : baseEnd_1447536 < baseStart_1447536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447569 : List Nat := [1, 2, 2, 1, 1, 1, 1, 6, 1, 7]
def baseStart_1447569 : Nat := 118140960795 + 1447569 * 2 ^ 59
def prefixEnd_1447569 : Nat := 4983230072969 + 3 ^ 40 * 1447569 * 2
def baseEnd_1447569 : Nat := 247766225849450704443419

theorem tailTrace_1447569 : CollatzResearch.WordTrace tailWord_1447569 prefixEnd_1447569 247766225849450704443419 := by
  unfold tailWord_1447569
  simp only [CollatzResearch.WordTrace]
  refine ⟨52797178892712212947713761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35198119261808141965142507 52797178892712212947713761)
  ·
    refine ⟨39597884169534159710785321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52797178892712212947713761 39597884169534159710785321)
    ·
      refine ⟨29698413127150619783088991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39597884169534159710785321 29698413127150619783088991)
      ·
        refine ⟨44547619690725929674633487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29698413127150619783088991 44547619690725929674633487)
        ·
          refine ⟨66821429536088894511950231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44547619690725929674633487 66821429536088894511950231)
          ·
            refine ⟨100232144304133341767925347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66821429536088894511950231 100232144304133341767925347)
            ·
              refine ⟨150348216456200012651888021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100232144304133341767925347 150348216456200012651888021)
              ·
                refine ⟨7047572646384375593057251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 150348216456200012651888021 7047572646384375593057251)
                ·
                  refine ⟨10571358969576563389585877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7047572646384375593057251 10571358969576563389585877)
                  ·
                    refine ⟨247766225849450704443419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10571358969576563389585877 247766225849450704443419)
                    ·
                      rfl

theorem cell23_1447569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 7].length) (baseStart_1447569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1447569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1447569 prefixEnd_1447569 := by exact prefixLift 1447569
  have htrace : WordTrace (prefixWord ++ tailWord_1447569) baseStart_1447569 baseEnd_1447569 := by
    simpa [prefixWord, tailWord_1447569, baseEnd_1447569] using wordTrace_append hprefix tailTrace_1447569
  have hstable : (prefixWord ++ tailWord_1447569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447569).length < 2 ^ (prefixWord ++ tailWord_1447569).sum := by decide
  have hdescent : baseEnd_1447569 < baseStart_1447569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447623 : List Nat := [1, 1, 4, 1, 1, 1, 5, 1, 2, 4, 2]
def baseStart_1447623 : Nat := 118140960795 + 1447623 * 2 ^ 59
def prefixEnd_1447623 : Nat := 4983230072969 + 3 ^ 40 * 1447623 * 2
def baseEnd_1447623 : Nat := 743326405503694902055009

theorem tailTrace_1447623 : CollatzResearch.WordTrace tailWord_1447623 prefixEnd_1447623 743326405503694902055009 := by
  unfold tailWord_1447623
  simp only [CollatzResearch.WordTrace]
  refine ⟨52799148434516580170179523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35199432289677720113453015 52799148434516580170179523)
  ·
    refine ⟨79198722651774870255269285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52799148434516580170179523 79198722651774870255269285)
    ·
      refine ⟨14849760497207788172862991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79198722651774870255269285 14849760497207788172862991)
      ·
        refine ⟨22274640745811682259294487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14849760497207788172862991 22274640745811682259294487)
        ·
          refine ⟨33411961118717523388941731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22274640745811682259294487 33411961118717523388941731)
          ·
            refine ⟨50117941678076285083412597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33411961118717523388941731 50117941678076285083412597)
            ·
              refine ⟨4698557032319651726569931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50117941678076285083412597 4698557032319651726569931)
              ·
                refine ⟨7047835548479477589854897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4698557032319651726569931 7047835548479477589854897)
                ·
                  refine ⟨5285876661359608192391173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7047835548479477589854897 5285876661359608192391173)
                  ·
                    refine ⟨991101874004926536073345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5285876661359608192391173 991101874004926536073345)
                    ·
                      refine ⟨743326405503694902055009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 991101874004926536073345 743326405503694902055009)
                      ·
                        rfl

theorem cell23_1447623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 2, 4, 2].length) (baseStart_1447623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1447623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1447623 prefixEnd_1447623 := by exact prefixLift 1447623
  have htrace : WordTrace (prefixWord ++ tailWord_1447623) baseStart_1447623 baseEnd_1447623 := by
    simpa [prefixWord, tailWord_1447623, baseEnd_1447623] using wordTrace_append hprefix tailTrace_1447623
  have hstable : (prefixWord ++ tailWord_1447623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447623).length < 2 ^ (prefixWord ++ tailWord_1447623).sum := by decide
  have hdescent : baseEnd_1447623 < baseStart_1447623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447633 : List Nat := [1, 2, 2, 1, 2, 5, 1, 2, 3, 4]
def baseStart_1447633 : Nat := 118140960795 + 1447633 * 2 ^ 59
def prefixEnd_1447633 : Nat := 4983230072969 + 3 ^ 40 * 1447633 * 2
def baseEnd_1447633 : Nat := 247777180103413287643321

theorem tailTrace_1447633 : CollatzResearch.WordTrace tailWord_1447633 prefixEnd_1447633 247777180103413287643321 := by
  unfold tailWord_1447633
  simp only [CollatzResearch.WordTrace]
  refine ⟨52799513164480351878043553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35199675442986901252029035 52799513164480351878043553)
  ·
    refine ⟨39599634873360263908532665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52799513164480351878043553 39599634873360263908532665)
    ·
      refine ⟨29699726155020197931399499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39599634873360263908532665 29699726155020197931399499)
      ·
        refine ⟨44549589232530296897099249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29699726155020197931399499 44549589232530296897099249)
        ·
          refine ⟨33412191924397722672824437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44549589232530296897099249 33412191924397722672824437)
          ·
            refine ⟨3132392992912286500577291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33412191924397722672824437 3132392992912286500577291)
            ·
              refine ⟨4698589489368429750865937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3132392992912286500577291 4698589489368429750865937)
              ·
                refine ⟨3523942117026322313149453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4698589489368429750865937 3523942117026322313149453)
                ·
                  refine ⟨1321478293884870867431045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3523942117026322313149453 1321478293884870867431045)
                  ·
                    refine ⟨247777180103413287643321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1321478293884870867431045 247777180103413287643321)
                    ·
                      rfl

theorem cell23_1447633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 2, 3, 4].length) (baseStart_1447633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1447633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1447633 prefixEnd_1447633 := by exact prefixLift 1447633
  have htrace : WordTrace (prefixWord ++ tailWord_1447633) baseStart_1447633 baseEnd_1447633 := by
    simpa [prefixWord, tailWord_1447633, baseEnd_1447633] using wordTrace_append hprefix tailTrace_1447633
  have hstable : (prefixWord ++ tailWord_1447633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447633).length < 2 ^ (prefixWord ++ tailWord_1447633).sum := by decide
  have hdescent : baseEnd_1447633 < baseStart_1447633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447666 : List Nat := [3, 2, 1, 3, 1, 1, 1, 1, 1, 1, 8]
def baseStart_1447666 : Nat := 118140960795 + 1447666 * 2 ^ 59
def prefixEnd_1447666 : Nat := 4983230072969 + 3 ^ 40 * 1447666 * 2
def baseEnd_1447666 : Nat := 743348485171838233817311

theorem tailTrace_1447666 : CollatzResearch.WordTrace tailWord_1447666 prefixEnd_1447666 743348485171838233817311 := by
  unfold tailWord_1447666
  simp only [CollatzResearch.WordTrace]
  refine ⟨13200179193340199628498713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35200477848907199009329901 13200179193340199628498713)
  ·
    refine ⟨9900134395005149721374035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13200179193340199628498713 9900134395005149721374035)
    ·
      refine ⟨14850201592507724582061053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9900134395005149721374035 14850201592507724582061053)
      ·
        refine ⟨5568825597190396718272895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14850201592507724582061053 5568825597190396718272895)
        ·
          refine ⟨8353238395785595077409343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5568825597190396718272895 8353238395785595077409343)
          ·
            refine ⟨12529857593678392616114015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8353238395785595077409343 12529857593678392616114015)
            ·
              refine ⟨18794786390517588924171023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12529857593678392616114015 18794786390517588924171023)
              ·
                refine ⟨28192179585776383386256535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18794786390517588924171023 28192179585776383386256535)
                ·
                  refine ⟨42288269378664575079384803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28192179585776383386256535 42288269378664575079384803)
                  ·
                    refine ⟨63432404067996862619077205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42288269378664575079384803 63432404067996862619077205)
                    ·
                      refine ⟨743348485171838233817311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 63432404067996862619077205 743348485171838233817311)
                      ·
                        rfl

theorem cell23_1447666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_1447666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1447666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1447666 prefixEnd_1447666 := by exact prefixLift 1447666
  have htrace : WordTrace (prefixWord ++ tailWord_1447666) baseStart_1447666 baseEnd_1447666 := by
    simpa [prefixWord, tailWord_1447666, baseEnd_1447666] using wordTrace_append hprefix tailTrace_1447666
  have hstable : (prefixWord ++ tailWord_1447666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447666).length < 2 ^ (prefixWord ++ tailWord_1447666).sum := by decide
  have hdescent : baseEnd_1447666 < baseStart_1447666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447683 : List Nat := [1, 1, 1, 3, 2, 2, 3, 2, 1, 5, 2]
def baseStart_1447683 : Nat := 118140960795 + 1447683 * 2 ^ 59
def prefixEnd_1447683 : Nat := 4983230072969 + 3 ^ 40 * 1447683 * 2
def baseEnd_1447683 : Nat := 743357214342964667304733

theorem tailTrace_1447683 : CollatzResearch.WordTrace tailWord_1447683 prefixEnd_1447683 743357214342964667304733 := by
  unfold tailWord_1447683
  simp only [CollatzResearch.WordTrace]
  refine ⟨52801336814299210417363703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35200891209532806944909135 52801336814299210417363703)
  ·
    refine ⟨79202005221448815626045555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52801336814299210417363703 79202005221448815626045555)
    ·
      refine ⟨118803007832173223439068333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79202005221448815626045555 118803007832173223439068333)
      ·
        refine ⟨44551127937064958789650625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118803007832173223439068333 44551127937064958789650625)
        ·
          refine ⟨33413345952798719092237969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44551127937064958789650625 33413345952798719092237969)
          ·
            refine ⟨25060009464599039319178477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33413345952798719092237969 25060009464599039319178477)
            ·
              refine ⟨9397503549224639744691929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25060009464599039319178477 9397503549224639744691929)
              ·
                refine ⟨7048127661918479808518947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9397503549224639744691929 7048127661918479808518947)
                ·
                  refine ⟨10572191492877719712778421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7048127661918479808518947 10572191492877719712778421)
                  ·
                    refine ⟨991142952457286223072977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10572191492877719712778421 991142952457286223072977)
                    ·
                      refine ⟨743357214342964667304733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 991142952457286223072977 743357214342964667304733)
                      ·
                        rfl

theorem cell23_1447683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 5, 2].length) (baseStart_1447683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1447683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1447683 prefixEnd_1447683 := by exact prefixLift 1447683
  have htrace : WordTrace (prefixWord ++ tailWord_1447683) baseStart_1447683 baseEnd_1447683 := by
    simpa [prefixWord, tailWord_1447683, baseEnd_1447683] using wordTrace_append hprefix tailTrace_1447683
  have hstable : (prefixWord ++ tailWord_1447683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447683).length < 2 ^ (prefixWord ++ tailWord_1447683).sum := by decide
  have hdescent : baseEnd_1447683 < baseStart_1447683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447690 : List Nat := [3, 1, 2, 2, 1, 3, 2, 2, 3, 1, 3]
def baseStart_1447690 : Nat := 118140960795 + 1447690 * 2 ^ 59
def prefixEnd_1447690 : Nat := 4983230072969 + 3 ^ 40 * 1447690 * 2
def baseEnd_1447690 : Nat := 743360808707546139917201

theorem tailTrace_1447690 : CollatzResearch.WordTrace tailWord_1447690 prefixEnd_1447690 743360808707546139917201 := by
  unfold tailWord_1447690
  simp only [CollatzResearch.WordTrace]
  refine ⟨13200398031318462653217131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35201061416849233741912349 13200398031318462653217131)
  ·
    refine ⟨19800597046977693979825697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13200398031318462653217131 19800597046977693979825697)
    ·
      refine ⟨14850447785233270484869273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19800597046977693979825697 14850447785233270484869273)
      ·
        refine ⟨11137835838924952863651955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14850447785233270484869273 11137835838924952863651955)
        ·
          refine ⟨16706753758387429295477933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11137835838924952863651955 16706753758387429295477933)
          ·
            refine ⟨6265032659395285985804225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16706753758387429295477933 6265032659395285985804225)
            ·
              refine ⟨4698774494546464489353169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6265032659395285985804225 4698774494546464489353169)
              ·
                refine ⟨3524080870909848367014877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4698774494546464489353169 3524080870909848367014877)
                ·
                  refine ⟨1321530326591193137630579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3524080870909848367014877 1321530326591193137630579)
                  ·
                    refine ⟨1982295489886789706445869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1321530326591193137630579 1982295489886789706445869)
                    ·
                      refine ⟨743360808707546139917201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1982295489886789706445869 743360808707546139917201)
                      ·
                        rfl

theorem cell23_1447690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 2, 3, 1, 3].length) (baseStart_1447690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1447690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1447690 prefixEnd_1447690 := by exact prefixLift 1447690
  have htrace : WordTrace (prefixWord ++ tailWord_1447690) baseStart_1447690 baseEnd_1447690 := by
    simpa [prefixWord, tailWord_1447690, baseEnd_1447690] using wordTrace_append hprefix tailTrace_1447690
  have hstable : (prefixWord ++ tailWord_1447690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447690).length < 2 ^ (prefixWord ++ tailWord_1447690).sum := by decide
  have hdescent : baseEnd_1447690 < baseStart_1447690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447724 : List Nat := [2, 2, 1, 1, 1, 6, 3, 2, 1, 1, 3]
def baseStart_1447724 : Nat := 118140960795 + 1447724 * 2 ^ 59
def prefixEnd_1447724 : Nat := 4983230072969 + 3 ^ 40 * 1447724 * 2
def baseEnd_1447724 : Nat := 743378267049799006892045

theorem tailTrace_1447724 : CollatzResearch.WordTrace tailWord_1447724 prefixEnd_1447724 743378267049799006892045 := by
  unfold tailWord_1447724
  simp only [CollatzResearch.WordTrace]
  refine ⟨26401416103575337209803113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35201888138100449613070817 26401416103575337209803113)
  ·
    refine ⟨19801062077681502907352335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26401416103575337209803113 19801062077681502907352335)
    ·
      refine ⟨29701593116522254361028503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19801062077681502907352335 29701593116522254361028503)
      ·
        refine ⟨44552389674783381541542755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29701593116522254361028503 44552389674783381541542755)
        ·
          refine ⟨66828584512175072312314133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44552389674783381541542755 66828584512175072312314133)
          ·
            refine ⟨3132589899008206514639725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 66828584512175072312314133 3132589899008206514639725)
            ·
              refine ⟨1174721212128077442989897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3132589899008206514639725 1174721212128077442989897)
              ·
                refine ⟨881040909096058082242423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1174721212128077442989897 881040909096058082242423)
                ·
                  refine ⟨1321561363644087123363635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 881040909096058082242423 1321561363644087123363635)
                  ·
                    refine ⟨1982342045466130685045453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1321561363644087123363635 1982342045466130685045453)
                    ·
                      refine ⟨743378267049799006892045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1982342045466130685045453 743378267049799006892045)
                      ·
                        rfl

theorem cell23_1447724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 3, 2, 1, 1, 3].length) (baseStart_1447724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1447724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1447724 prefixEnd_1447724 := by exact prefixLift 1447724
  have htrace : WordTrace (prefixWord ++ tailWord_1447724) baseStart_1447724 baseEnd_1447724 := by
    simpa [prefixWord, tailWord_1447724, baseEnd_1447724] using wordTrace_append hprefix tailTrace_1447724
  have hstable : (prefixWord ++ tailWord_1447724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447724).length < 2 ^ (prefixWord ++ tailWord_1447724).sum := by decide
  have hdescent : baseEnd_1447724 < baseStart_1447724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447736 : List Nat := [2, 1, 2, 1, 3, 3, 1, 10]
def baseStart_1447736 : Nat := 118140960795 + 1447736 * 2 ^ 59
def prefixEnd_1447736 : Nat := 4983230072969 + 3 ^ 40 * 1447736 * 2
def baseEnd_1447736 : Nat := 27532756622876035553407

theorem tailTrace_1447736 : CollatzResearch.WordTrace tailWord_1447736 prefixEnd_1447736 27532756622876035553407 := by
  unfold tailWord_1447736
  simp only [CollatzResearch.WordTrace]
  refine ⟨26401634941553600234521531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35202179922071466979362041 26401634941553600234521531)
  ·
    refine ⟨39602452412330400351782297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26401634941553600234521531 39602452412330400351782297)
    ·
      refine ⟨29701839309247800263836723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39602452412330400351782297 29701839309247800263836723)
      ·
        refine ⟨44552758963871700395755085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29701839309247800263836723 44552758963871700395755085)
        ·
          refine ⟨16707284611451887648408157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44552758963871700395755085 16707284611451887648408157)
          ·
            refine ⟨6265231729294457868153059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16707284611451887648408157 6265231729294457868153059)
            ·
              refine ⟨9397847593941686802229589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6265231729294457868153059 9397847593941686802229589)
              ·
                refine ⟨27532756622876035553407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 9397847593941686802229589 27532756622876035553407)
                ·
                  rfl

theorem cell23_1447736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 10].length) (baseStart_1447736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1447736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1447736 prefixEnd_1447736 := by exact prefixLift 1447736
  have htrace : WordTrace (prefixWord ++ tailWord_1447736) baseStart_1447736 baseEnd_1447736 := by
    simpa [prefixWord, tailWord_1447736, baseEnd_1447736] using wordTrace_append hprefix tailTrace_1447736
  have hstable : (prefixWord ++ tailWord_1447736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447736).length < 2 ^ (prefixWord ++ tailWord_1447736).sum := by decide
  have hdescent : baseEnd_1447736 < baseStart_1447736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447767 : List Nat := [1, 1, 3, 2, 6, 1, 1, 1, 1, 1, 5]
def baseStart_1447767 : Nat := 118140960795 + 1447767 * 2 ^ 59
def prefixEnd_1447767 : Nat := 4983230072969 + 3 ^ 40 * 1447767 * 2
def baseEnd_1447767 : Nat := 743400346717942338654347

theorem tailTrace_1447767 : CollatzResearch.WordTrace tailWord_1447767 prefixEnd_1447767 743400346717942338654347 := by
  unfold tailWord_1447767
  simp only [CollatzResearch.WordTrace]
  refine ⟨52804400545994892763421555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35202933697329928508947703 52804400545994892763421555)
  ·
    refine ⟨79206600818992339145132333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52804400545994892763421555 79206600818992339145132333)
    ·
      refine ⟨29702475307122127179424625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79206600818992339145132333 29702475307122127179424625)
      ·
        refine ⟨22276856480341595384568469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29702475307122127179424625 22276856480341595384568469)
        ·
          refine ⟨1044227647516012283651647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 22276856480341595384568469 1044227647516012283651647)
          ·
            refine ⟨1566341471274018425477471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1044227647516012283651647 1566341471274018425477471)
            ·
              refine ⟨2349512206911027638216207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1566341471274018425477471 2349512206911027638216207)
              ·
                refine ⟨3524268310366541457324311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2349512206911027638216207 3524268310366541457324311)
                ·
                  refine ⟨5286402465549812185986467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3524268310366541457324311 5286402465549812185986467)
                  ·
                    refine ⟨7929603698324718278979701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5286402465549812185986467 7929603698324718278979701)
                    ·
                      refine ⟨743400346717942338654347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7929603698324718278979701 743400346717942338654347)
                      ·
                        rfl

theorem cell23_1447767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 1, 1, 1, 5].length) (baseStart_1447767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1447767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1447767 prefixEnd_1447767 := by exact prefixLift 1447767
  have htrace : WordTrace (prefixWord ++ tailWord_1447767) baseStart_1447767 baseEnd_1447767 := by
    simpa [prefixWord, tailWord_1447767, baseEnd_1447767] using wordTrace_append hprefix tailTrace_1447767
  have hstable : (prefixWord ++ tailWord_1447767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447767).length < 2 ^ (prefixWord ++ tailWord_1447767).sum := by decide
  have hdescent : baseEnd_1447767 < baseStart_1447767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447797 : List Nat := [1, 3, 4, 1, 1, 1, 1, 5, 2, 1, 3]
def baseStart_1447797 : Nat := 118140960795 + 1447797 * 2 ^ 59
def prefixEnd_1447797 : Nat := 4983230072969 + 3 ^ 40 * 1447797 * 2
def baseEnd_1447797 : Nat := 743415751137577221279209

theorem tailTrace_1447797 : CollatzResearch.WordTrace tailWord_1447797 prefixEnd_1447797 743415751137577221279209 := by
  unfold tailWord_1447797
  simp only [CollatzResearch.WordTrace]
  refine ⟨52805494735886207887013645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35203663157257471924675763 52805494735886207887013645)
  ·
    refine ⟨19802060525957327957630117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52805494735886207887013645 19802060525957327957630117)
    ·
      refine ⟨3712886348616998992055647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19802060525957327957630117 3712886348616998992055647)
      ·
        refine ⟨5569329522925498488083471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3712886348616998992055647 5569329522925498488083471)
        ·
          refine ⟨8353994284388247732125207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5569329522925498488083471 8353994284388247732125207)
          ·
            refine ⟨12530991426582371598187811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8353994284388247732125207 12530991426582371598187811)
            ·
              refine ⟨18796487139873557397281717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12530991426582371598187811 18796487139873557397281717)
              ·
                refine ⟨1762170669363146005995161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18796487139873557397281717 1762170669363146005995161)
                ·
                  refine ⟨1321628002022359504496371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1762170669363146005995161 1321628002022359504496371)
                  ·
                    refine ⟨1982442003033539256744557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1321628002022359504496371 1982442003033539256744557)
                    ·
                      refine ⟨743415751137577221279209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1982442003033539256744557 743415751137577221279209)
                      ·
                        rfl

theorem cell23_1447797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_1447797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1447797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1447797 prefixEnd_1447797 := by exact prefixLift 1447797
  have htrace : WordTrace (prefixWord ++ tailWord_1447797) baseStart_1447797 baseEnd_1447797 := by
    simpa [prefixWord, tailWord_1447797, baseEnd_1447797] using wordTrace_append hprefix tailTrace_1447797
  have hstable : (prefixWord ++ tailWord_1447797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447797).length < 2 ^ (prefixWord ++ tailWord_1447797).sum := by decide
  have hdescent : baseEnd_1447797 < baseStart_1447797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447833 : List Nat := [1, 2, 1, 2, 1, 3, 3, 2, 2, 2, 4]
def baseStart_1447833 : Nat := 118140960795 + 1447833 * 2 ^ 59
def prefixEnd_1447833 : Nat := 4983230072969 + 3 ^ 40 * 1447833 * 2
def baseEnd_1447833 : Nat := 743434236441139080429043

theorem tailTrace_1447833 : CollatzResearch.WordTrace tailWord_1447833 prefixEnd_1447833 743434236441139080429043 := by
  unfold tailWord_1447833
  simp only [CollatzResearch.WordTrace]
  refine ⟨52806807763755786035324153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35204538509170524023549435 52806807763755786035324153)
  ·
    refine ⟨39605105822816839526493115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52806807763755786035324153 39605105822816839526493115)
    ·
      refine ⟨59407658734225259289739673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39605105822816839526493115 59407658734225259289739673)
      ·
        refine ⟨44555744050668944467304755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59407658734225259289739673 44555744050668944467304755)
        ·
          refine ⟨66833616076003416700957133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44555744050668944467304755 66833616076003416700957133)
          ·
            refine ⟨25062606028501281262858925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66833616076003416700957133 25062606028501281262858925)
            ·
              refine ⟨9398477260687980473572097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25062606028501281262858925 9398477260687980473572097)
              ·
                refine ⟨7048857945515985355179073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9398477260687980473572097 7048857945515985355179073)
                ·
                  refine ⟨5286643459136989016384305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7048857945515985355179073 5286643459136989016384305)
                  ·
                    refine ⟨3964982594352741762288229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5286643459136989016384305 3964982594352741762288229)
                    ·
                      refine ⟨743434236441139080429043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3964982594352741762288229 743434236441139080429043)
                      ·
                        rfl

theorem cell23_1447833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 2, 2, 4].length) (baseStart_1447833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1447833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1447833 prefixEnd_1447833 := by exact prefixLift 1447833
  have htrace : WordTrace (prefixWord ++ tailWord_1447833) baseStart_1447833 baseEnd_1447833 := by
    simpa [prefixWord, tailWord_1447833, baseEnd_1447833] using wordTrace_append hprefix tailTrace_1447833
  have hstable : (prefixWord ++ tailWord_1447833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447833).length < 2 ^ (prefixWord ++ tailWord_1447833).sum := by decide
  have hdescent : baseEnd_1447833 < baseStart_1447833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447848 : List Nat := [2, 1, 6, 2, 1, 1, 3, 1, 2, 1, 3]
def baseStart_1447848 : Nat := 118140960795 + 1447848 * 2 ^ 59
def prefixEnd_1447848 : Nat := 4983230072969 + 3 ^ 40 * 1447848 * 2
def baseEnd_1447848 : Nat := 743441938650956521741475

theorem tailTrace_1447848 : CollatzResearch.WordTrace tailWord_1447848 prefixEnd_1447848 743441938650956521741475 := by
  unfold tailWord_1447848
  simp only [CollatzResearch.WordTrace]
  refine ⟨26403677429350721798560099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35204903239134295731413465 26403677429350721798560099)
  ·
    refine ⟨39605516144026082697840149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26403677429350721798560099 39605516144026082697840149)
    ·
      refine ⟨1856508569251222626461257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 39605516144026082697840149 1856508569251222626461257)
      ·
        refine ⟨1392381426938416969845943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1856508569251222626461257 1392381426938416969845943)
        ·
          refine ⟨2088572140407625454768915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1392381426938416969845943 2088572140407625454768915)
          ·
            refine ⟨3132858210611438182153373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2088572140407625454768915 3132858210611438182153373)
            ·
              refine ⟨1174821828979289318307515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3132858210611438182153373 1174821828979289318307515)
              ·
                refine ⟨1762232743468933977461273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1174821828979289318307515 1762232743468933977461273)
                ·
                  refine ⟨1321674557601700483095955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1762232743468933977461273 1321674557601700483095955)
                  ·
                    refine ⟨1982511836402550724643933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1321674557601700483095955 1982511836402550724643933)
                    ·
                      refine ⟨743441938650956521741475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1982511836402550724643933 743441938650956521741475)
                      ·
                        rfl

theorem cell23_1447848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_1447848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1447848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1447848 prefixEnd_1447848 := by exact prefixLift 1447848
  have htrace : WordTrace (prefixWord ++ tailWord_1447848) baseStart_1447848 baseEnd_1447848 := by
    simpa [prefixWord, tailWord_1447848, baseEnd_1447848] using wordTrace_append hprefix tailTrace_1447848
  have hstable : (prefixWord ++ tailWord_1447848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447848).length < 2 ^ (prefixWord ++ tailWord_1447848).sum := by decide
  have hdescent : baseEnd_1447848 < baseStart_1447848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447883 : List Nat := [1, 1, 1, 1, 3, 4, 2, 2, 1, 2, 5]
def baseStart_1447883 : Nat := 118140960795 + 1447883 * 2 ^ 59
def prefixEnd_1447883 : Nat := 4983230072969 + 3 ^ 40 * 1447883 * 2
def baseEnd_1447883 : Nat := 743459910473863884803813

theorem tailTrace_1447883 : CollatzResearch.WordTrace tailWord_1447883 prefixEnd_1447883 743459910473863884803813 := by
  unfold tailWord_1447883
  simp only [CollatzResearch.WordTrace]
  refine ⟨52808631413574644574644303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35205754275716429716429535 52808631413574644574644303)
  ·
    refine ⟨79212947120361966861966455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52808631413574644574644303 79212947120361966861966455)
    ·
      refine ⟨118819420680542950292949683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79212947120361966861966455 118819420680542950292949683)
      ·
        refine ⟨178229131020814425439424525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118819420680542950292949683 178229131020814425439424525)
        ·
          refine ⟨66835924132805409539784197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178229131020814425439424525 66835924132805409539784197)
          ·
            refine ⟨12531735774901014288709537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66835924132805409539784197 12531735774901014288709537)
            ·
              refine ⟨9398801831175760716532153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12531735774901014288709537 9398801831175760716532153)
              ·
                refine ⟨7049101373381820537399115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9398801831175760716532153 7049101373381820537399115)
                ·
                  refine ⟨10573652060072730806098673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7049101373381820537399115 10573652060072730806098673)
                  ·
                    refine ⟨7930239045054548104574005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10573652060072730806098673 7930239045054548104574005)
                    ·
                      refine ⟨743459910473863884803813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7930239045054548104574005 743459910473863884803813)
                      ·
                        rfl

theorem cell23_1447883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 2, 5].length) (baseStart_1447883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1447883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1447883 prefixEnd_1447883 := by exact prefixLift 1447883
  have htrace : WordTrace (prefixWord ++ tailWord_1447883) baseStart_1447883 baseEnd_1447883 := by
    simpa [prefixWord, tailWord_1447883, baseEnd_1447883] using wordTrace_append hprefix tailTrace_1447883
  have hstable : (prefixWord ++ tailWord_1447883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447883).length < 2 ^ (prefixWord ++ tailWord_1447883).sum := by decide
  have hdescent : baseEnd_1447883 < baseStart_1447883 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447894 : List Nat := [5, 2, 1, 1, 3, 2, 1, 1, 7]
def baseStart_1447894 : Nat := 118140960795 + 1447894 * 2 ^ 59
def prefixEnd_1447894 : Nat := 4983230072969 + 3 ^ 40 * 1447894 * 2
def baseEnd_1447894 : Nat := 82607284306784815751807

theorem tailTrace_1447894 : CollatzResearch.WordTrace tailWord_1447894 prefixEnd_1447894 82607284306784815751807 := by
  unfold tailWord_1447894
  simp only [CollatzResearch.WordTrace]
  refine ⟨3300564538533424590830921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35206021744356528968863157 3300564538533424590830921)
  ·
    refine ⟨2475423403900068443123191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3300564538533424590830921 2475423403900068443123191)
    ·
      refine ⟨3713135105850102664684787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2475423403900068443123191 3713135105850102664684787)
      ·
        refine ⟨5569702658775153997027181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3713135105850102664684787 5569702658775153997027181)
        ·
          refine ⟨2088638497040682748885193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5569702658775153997027181 2088638497040682748885193)
          ·
            refine ⟨1566478872780512061663895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2088638497040682748885193 1566478872780512061663895)
            ·
              refine ⟨2349718309170768092495843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1566478872780512061663895 2349718309170768092495843)
              ·
                refine ⟨3524577463756152138743765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2349718309170768092495843 3524577463756152138743765)
                ·
                  refine ⟨82607284306784815751807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3524577463756152138743765 82607284306784815751807)
                  ·
                    rfl

theorem cell23_1447894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_1447894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1447894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1447894 prefixEnd_1447894 := by exact prefixLift 1447894
  have htrace : WordTrace (prefixWord ++ tailWord_1447894) baseStart_1447894 baseEnd_1447894 := by
    simpa [prefixWord, tailWord_1447894, baseEnd_1447894] using wordTrace_append hprefix tailTrace_1447894
  have hstable : (prefixWord ++ tailWord_1447894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447894).length < 2 ^ (prefixWord ++ tailWord_1447894).sum := by decide
  have hdescent : baseEnd_1447894 < baseStart_1447894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447920 : List Nat := [2, 1, 1, 1, 3, 2, 2, 4, 3, 4]
def baseStart_1447920 : Nat := 118140960795 + 1447920 * 2 ^ 59
def prefixEnd_1447920 : Nat := 4983230072969 + 3 ^ 40 * 1447920 * 2
def baseEnd_1447920 : Nat := 247826303086026746680381

theorem tailTrace_1447920 : CollatzResearch.WordTrace tailWord_1447920 prefixEnd_1447920 247826303086026746680381 := by
  unfold tailWord_1447920
  simp only [CollatzResearch.WordTrace]
  refine ⟨26404990457220299946870607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35206653942960399929160809 26404990457220299946870607)
  ·
    refine ⟨39607485685830449920305911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26404990457220299946870607 39607485685830449920305911)
    ·
      refine ⟨59411228528745674880458867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39607485685830449920305911 59411228528745674880458867)
      ·
        refine ⟨89116842793118512320688301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59411228528745674880458867 89116842793118512320688301)
        ·
          refine ⟨33418816047419442120258113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89116842793118512320688301 33418816047419442120258113)
          ·
            refine ⟨25064112035564581590193585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33418816047419442120258113 25064112035564581590193585)
            ·
              refine ⟨18798084026673436192645189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25064112035564581590193585 18798084026673436192645189)
              ·
                refine ⟨3524640755001269286120973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18798084026673436192645189 3524640755001269286120973)
                ·
                  refine ⟨1321740283125475982295365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3524640755001269286120973 1321740283125475982295365)
                  ·
                    refine ⟨247826303086026746680381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1321740283125475982295365 247826303086026746680381)
                    ·
                      rfl

theorem cell23_1447920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 4, 3, 4].length) (baseStart_1447920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1447920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1447920 prefixEnd_1447920 := by exact prefixLift 1447920
  have htrace : WordTrace (prefixWord ++ tailWord_1447920) baseStart_1447920 baseEnd_1447920 := by
    simpa [prefixWord, tailWord_1447920, baseEnd_1447920] using wordTrace_append hprefix tailTrace_1447920
  have hstable : (prefixWord ++ tailWord_1447920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447920).length < 2 ^ (prefixWord ++ tailWord_1447920).sum := by decide
  have hdescent : baseEnd_1447920 < baseStart_1447920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447923 : List Nat := [1, 1, 1, 2, 2, 2, 1, 3, 2, 4, 4]
def baseStart_1447923 : Nat := 118140960795 + 1447923 * 2 ^ 59
def prefixEnd_1447923 : Nat := 4983230072969 + 3 ^ 40 * 1447923 * 2
def baseEnd_1447923 : Nat := 743480449700043728303629

theorem tailTrace_1447923 : CollatzResearch.WordTrace tailWord_1447923 prefixEnd_1447923 743480449700043728303629 := by
  unfold tailWord_1447923
  simp only [CollatzResearch.WordTrace]
  refine ⟨52810090333429731406100423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35206726888953154270733615 52810090333429731406100423)
  ·
    refine ⟨79215135500144597109150635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52810090333429731406100423 79215135500144597109150635)
    ·
      refine ⟨118822703250216895663725953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79215135500144597109150635 118822703250216895663725953)
      ·
        refine ⟨89117027437662671747794465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118822703250216895663725953 89117027437662671747794465)
        ·
          refine ⟨66837770578247003810845849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89117027437662671747794465 66837770578247003810845849)
          ·
            refine ⟨50128327933685252858134387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66837770578247003810845849 50128327933685252858134387)
            ·
              refine ⟨75192491900527879287201581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50128327933685252858134387 75192491900527879287201581)
              ·
                refine ⟨28197184462697954732700593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75192491900527879287201581 28197184462697954732700593)
                ·
                  refine ⟨21147888347023466049525445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28197184462697954732700593 21147888347023466049525445)
                  ·
                    refine ⟨3965229065066899884286021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21147888347023466049525445 3965229065066899884286021)
                    ·
                      refine ⟨743480449700043728303629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3965229065066899884286021 743480449700043728303629)
                      ·
                        rfl

theorem cell23_1447923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 4, 4].length) (baseStart_1447923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1447923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1447923 prefixEnd_1447923 := by exact prefixLift 1447923
  have htrace : WordTrace (prefixWord ++ tailWord_1447923) baseStart_1447923 baseEnd_1447923 := by
    simpa [prefixWord, tailWord_1447923, baseEnd_1447923] using wordTrace_append hprefix tailTrace_1447923
  have hstable : (prefixWord ++ tailWord_1447923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447923).length < 2 ^ (prefixWord ++ tailWord_1447923).sum := by decide
  have hdescent : baseEnd_1447923 < baseStart_1447923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447933 : List Nat := [1, 4, 1, 1, 1, 2, 2, 1, 10]
def baseStart_1447933 : Nat := 118140960795 + 1447933 * 2 ^ 59
def prefixEnd_1447933 : Nat := 4983230072969 + 3 ^ 40 * 1447933 * 2
def baseEnd_1447933 : Nat := 82609509389620965464287

theorem tailTrace_1447933 : CollatzResearch.WordTrace tailWord_1447933 prefixEnd_1447933 82609509389620965464287 := by
  unfold tailWord_1447933
  simp only [CollatzResearch.WordTrace]
  refine ⟨52810455063393503113964453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35206970042262335409309635 52810455063393503113964453)
  ·
    refine ⟨9901960324386281833868335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52810455063393503113964453 9901960324386281833868335)
    ·
      refine ⟨14852940486579422750802503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9901960324386281833868335 14852940486579422750802503)
      ·
        refine ⟨22279410729869134126203755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14852940486579422750802503 22279410729869134126203755)
        ·
          refine ⟨33419116094803701189305633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22279410729869134126203755 33419116094803701189305633)
          ·
            refine ⟨25064337071102775891979225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33419116094803701189305633 25064337071102775891979225)
            ·
              refine ⟨18798252803327081918984419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25064337071102775891979225 18798252803327081918984419)
              ·
                refine ⟨28197379204990622878476629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18798252803327081918984419 28197379204990622878476629)
                ·
                  refine ⟨82609509389620965464287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 28197379204990622878476629 82609509389620965464287)
                  ·
                    rfl

theorem cell23_1447933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 10].length) (baseStart_1447933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1447933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1447933 prefixEnd_1447933 := by exact prefixLift 1447933
  have htrace : WordTrace (prefixWord ++ tailWord_1447933) baseStart_1447933 baseEnd_1447933 := by
    simpa [prefixWord, tailWord_1447933, baseEnd_1447933] using wordTrace_append hprefix tailTrace_1447933
  have hstable : (prefixWord ++ tailWord_1447933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447933).length < 2 ^ (prefixWord ++ tailWord_1447933).sum := by decide
  have hdescent : baseEnd_1447933 < baseStart_1447933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447988 : List Nat := [2, 5, 1, 2, 2, 1, 2, 3, 1, 4]
def baseStart_1447988 : Nat := 118140960795 + 1447988 * 2 ^ 59
def prefixEnd_1447988 : Nat := 4983230072969 + 3 ^ 40 * 1447988 * 2
def baseEnd_1447988 : Nat := 247837941980861991330277

theorem tailTrace_1447988 : CollatzResearch.WordTrace tailWord_1447988 prefixEnd_1447988 247837941980861991330277 := by
  unfold tailWord_1447988
  simp only [CollatzResearch.WordTrace]
  refine ⟨26406230539097123753608309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35208307385462831671477745 26406230539097123753608309)
  ·
    refine ⟨2475584113040355351900779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26406230539097123753608309 2475584113040355351900779)
    ·
      refine ⟨3713376169560533027851169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2475584113040355351900779 3713376169560533027851169)
      ·
        refine ⟨2785032127170399770888377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3713376169560533027851169 2785032127170399770888377)
        ·
          refine ⟨2088774095377799828166283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2785032127170399770888377 2088774095377799828166283)
          ·
            refine ⟨3133161143066699742249425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2088774095377799828166283 3133161143066699742249425)
            ·
              refine ⟨2349870857300024806687069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3133161143066699742249425 2349870857300024806687069)
              ·
                refine ⟨881201571487509302507651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2349870857300024806687069 881201571487509302507651)
                ·
                  refine ⟨1321802357231263953761477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 881201571487509302507651 1321802357231263953761477)
                  ·
                    refine ⟨247837941980861991330277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1321802357231263953761477 247837941980861991330277)
                    ·
                      rfl

theorem cell23_1447988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_1447988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1447988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1447988 prefixEnd_1447988 := by exact prefixLift 1447988
  have htrace : WordTrace (prefixWord ++ tailWord_1447988) baseStart_1447988 baseEnd_1447988 := by
    simpa [prefixWord, tailWord_1447988, baseEnd_1447988] using wordTrace_append hprefix tailTrace_1447988
  have hstable : (prefixWord ++ tailWord_1447988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447988).length < 2 ^ (prefixWord ++ tailWord_1447988).sum := by decide
  have hdescent : baseEnd_1447988 < baseStart_1447988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447997 : List Nat := [1, 4, 1, 3, 1, 1, 3, 3, 1, 5]
def baseStart_1447997 : Nat := 118140960795 + 1447997 * 2 ^ 59
def prefixEnd_1447997 : Nat := 4983230072969 + 3 ^ 40 * 1447997 * 2
def baseEnd_1447997 : Nat := 247839482422825479592763

theorem tailTrace_1447997 : CollatzResearch.WordTrace tailWord_1447997 prefixEnd_1447997 247839482422825479592763 := by
  unfold tailWord_1447997
  simp only [CollatzResearch.WordTrace]
  refine ⟨52812789335161642044294245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35208526223441094696196163 52812789335161642044294245)
  ·
    refine ⟨9902398000342807883305171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52812789335161642044294245 9902398000342807883305171)
    ·
      refine ⟨14853597000514211824957757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9902398000342807883305171 14853597000514211824957757)
      ·
        refine ⟨5570098875192829434359159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14853597000514211824957757 5570098875192829434359159)
        ·
          refine ⟨8355148312789244151538739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5570098875192829434359159 8355148312789244151538739)
          ·
            refine ⟨12532722469183866227308109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8355148312789244151538739 12532722469183866227308109)
            ·
              refine ⟨4699770925943949835240541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12532722469183866227308109 4699770925943949835240541)
              ·
                refine ⟨1762414097228981188215203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4699770925943949835240541 1762414097228981188215203)
                ·
                  refine ⟨2643621145843471782322805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1762414097228981188215203 2643621145843471782322805)
                  ·
                    refine ⟨247839482422825479592763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2643621145843471782322805 247839482422825479592763)
                    ·
                      rfl

theorem cell23_1447997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 3, 1, 5].length) (baseStart_1447997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1447997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1447997 prefixEnd_1447997 := by exact prefixLift 1447997
  have htrace : WordTrace (prefixWord ++ tailWord_1447997) baseStart_1447997 baseEnd_1447997 := by
    simpa [prefixWord, tailWord_1447997, baseEnd_1447997] using wordTrace_append hprefix tailTrace_1447997
  have hstable : (prefixWord ++ tailWord_1447997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447997).length < 2 ^ (prefixWord ++ tailWord_1447997).sum := by decide
  have hdescent : baseEnd_1447997 < baseStart_1447997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448054 : List Nat := [5, 1, 1, 2, 1, 3, 2, 1, 1, 1, 5]
def baseStart_1448054 : Nat := 118140960795 + 1448054 * 2 ^ 59
def prefixEnd_1448054 : Nat := 4983230072969 + 3 ^ 40 * 1448054 * 2
def baseEnd_1448054 : Nat := 743547715665782715765527

theorem tailTrace_1448054 : CollatzResearch.WordTrace tailWord_1448054 prefixEnd_1448054 743547715665782715765527 := by
  unfold tailWord_1448054
  simp only [CollatzResearch.WordTrace]
  refine ⟨3300929268497196298694951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35209912197303427186079477 3300929268497196298694951)
  ·
    refine ⟨4951393902745794448042427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3300929268497196298694951 4951393902745794448042427)
    ·
      refine ⟨7427090854118691672063641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4951393902745794448042427 7427090854118691672063641)
      ·
        refine ⟨5570318140589018754047731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7427090854118691672063641 5570318140589018754047731)
        ·
          refine ⟨8355477210883528131071597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5570318140589018754047731 8355477210883528131071597)
          ·
            refine ⟨3133303954081323049151849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8355477210883528131071597 3133303954081323049151849)
            ·
              refine ⟨2349977965560992286863887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3133303954081323049151849 2349977965560992286863887)
              ·
                refine ⟨3524966948341488430295831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2349977965560992286863887 3524966948341488430295831)
                ·
                  refine ⟨5287450422512232645443747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3524966948341488430295831 5287450422512232645443747)
                  ·
                    refine ⟨7931175633768348968165621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5287450422512232645443747 7931175633768348968165621)
                    ·
                      refine ⟨743547715665782715765527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7931175633768348968165621 743547715665782715765527)
                      ·
                        rfl

theorem cell23_1448054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_1448054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1448054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1448054 prefixEnd_1448054 := by exact prefixLift 1448054
  have htrace : WordTrace (prefixWord ++ tailWord_1448054) baseStart_1448054 baseEnd_1448054 := by
    simpa [prefixWord, tailWord_1448054, baseEnd_1448054] using wordTrace_append hprefix tailTrace_1448054
  have hstable : (prefixWord ++ tailWord_1448054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448054).length < 2 ^ (prefixWord ++ tailWord_1448054).sum := by decide
  have hdescent : baseEnd_1448054 < baseStart_1448054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448078 : List Nat := [4, 1, 1, 3, 3, 2, 2, 1, 2, 4]
def baseStart_1448078 : Nat := 118140960795 + 1448078 * 2 ^ 59
def prefixEnd_1448078 : Nat := 4983230072969 + 3 ^ 40 * 1448078 * 2
def baseEnd_1448078 : Nat := 247853346400496873955139

theorem tailTrace_1448078 : CollatzResearch.WordTrace tailWord_1448078 prefixEnd_1448078 247853346400496873955139 := by
  unfold tailWord_1448078
  simp only [CollatzResearch.WordTrace]
  refine ⟨6601967955983524109749111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35210495765245461918661925 6601967955983524109749111)
  ·
    refine ⟨9902951933975286164623667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6601967955983524109749111 9902951933975286164623667)
    ·
      refine ⟨14854427900962929246935501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9902951933975286164623667 14854427900962929246935501)
      ·
        refine ⟨5570410462861098467600813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14854427900962929246935501 5570410462861098467600813)
        ·
          refine ⟨2088903923572911925350305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5570410462861098467600813 2088903923572911925350305)
          ·
            refine ⟨1566677942679683944012729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2088903923572911925350305 1566677942679683944012729)
            ·
              refine ⟨1175008457009762958009547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1566677942679683944012729 1175008457009762958009547)
              ·
                refine ⟨1762512685514644437014321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1175008457009762958009547 1762512685514644437014321)
                ·
                  refine ⟨1321884514135983327760741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1762512685514644437014321 1321884514135983327760741)
                  ·
                    refine ⟨247853346400496873955139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1321884514135983327760741 247853346400496873955139)
                    ·
                      rfl

theorem cell23_1448078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 2, 1, 2, 4].length) (baseStart_1448078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1448078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1448078 prefixEnd_1448078 := by exact prefixLift 1448078
  have htrace : WordTrace (prefixWord ++ tailWord_1448078) baseStart_1448078 baseEnd_1448078 := by
    simpa [prefixWord, tailWord_1448078, baseEnd_1448078] using wordTrace_append hprefix tailTrace_1448078
  have hstable : (prefixWord ++ tailWord_1448078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448078).length < 2 ^ (prefixWord ++ tailWord_1448078).sum := by decide
  have hdescent : baseEnd_1448078 < baseStart_1448078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448088 : List Nat := [2, 1, 2, 4, 4, 1, 1, 2, 1, 2, 3]
def baseStart_1448088 : Nat := 118140960795 + 1448088 * 2 ^ 59
def prefixEnd_1448088 : Nat := 4983230072969 + 3 ^ 40 * 1448088 * 2
def baseEnd_1448088 : Nat := 743565174008035582740371

theorem tailTrace_1448088 : CollatzResearch.WordTrace tailWord_1448088 prefixEnd_1448088 743565174008035582740371 := by
  unfold tailWord_1448088
  simp only [CollatzResearch.WordTrace]
  refine ⟨26408054188915982292928459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35210738918554643057237945 26408054188915982292928459)
  ·
    refine ⟨39612081283373973439392689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26408054188915982292928459 39612081283373973439392689)
    ·
      refine ⟨29709060962530480079544517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39612081283373973439392689 29709060962530480079544517)
      ·
        refine ⟨5570448930474465014914597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29709060962530480079544517 5570448930474465014914597)
        ·
          refine ⟨1044459174463962190296487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5570448930474465014914597 1044459174463962190296487)
          ·
            refine ⟨1566688761695943285444731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1044459174463962190296487 1566688761695943285444731)
            ·
              refine ⟨2350033142543914928167097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1566688761695943285444731 2350033142543914928167097)
              ·
                refine ⟨1762524856907936196125323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2350033142543914928167097 1762524856907936196125323)
                ·
                  refine ⟨2643787285361904294187985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1762524856907936196125323 2643787285361904294187985)
                  ·
                    refine ⟨1982840464021428220640989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2643787285361904294187985 1982840464021428220640989)
                    ·
                      refine ⟨743565174008035582740371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1982840464021428220640989 743565174008035582740371)
                      ·
                        rfl

theorem cell23_1448088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 2, 1, 2, 3].length) (baseStart_1448088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1448088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1448088 prefixEnd_1448088 := by exact prefixLift 1448088
  have htrace : WordTrace (prefixWord ++ tailWord_1448088) baseStart_1448088 baseEnd_1448088 := by
    simpa [prefixWord, tailWord_1448088, baseEnd_1448088] using wordTrace_append hprefix tailTrace_1448088
  have hstable : (prefixWord ++ tailWord_1448088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448088).length < 2 ^ (prefixWord ++ tailWord_1448088).sum := by decide
  have hdescent : baseEnd_1448088 < baseStart_1448088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448162 : List Nat := [3, 3, 4, 1, 1, 1, 1, 3, 1, 3, 2]
def baseStart_1448162 : Nat := 118140960795 + 1448162 * 2 ^ 59
def prefixEnd_1448162 : Nat := 4983230072969 + 3 ^ 40 * 1448162 * 2
def baseEnd_1448162 : Nat := 743603171576468293215031

theorem tailTrace_1448162 : CollatzResearch.WordTrace tailWord_1448162 prefixEnd_1448162 743603171576468293215031 := by
  unfold tailWord_1448162
  simp only [CollatzResearch.WordTrace]
  refine ⟨13204701844890968806012685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35212538253042583482700493 13204701844890968806012685)
  ·
    refine ⟨4951763191834113302254757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13204701844890968806012685 4951763191834113302254757)
    ·
      refine ⟨928455598468896244172767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4951763191834113302254757 928455598468896244172767)
      ·
        refine ⟨1392683397703344366259151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 928455598468896244172767 1392683397703344366259151)
        ·
          refine ⟨2089025096555016549388727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1392683397703344366259151 2089025096555016549388727)
          ·
            refine ⟨3133537644832524824083091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2089025096555016549388727 3133537644832524824083091)
            ·
              refine ⟨4700306467248787236124637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3133537644832524824083091 4700306467248787236124637)
              ·
                refine ⟨1762614925218295213546739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4700306467248787236124637 1762614925218295213546739)
                ·
                  refine ⟨2643922387827442820320109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1762614925218295213546739 2643922387827442820320109)
                  ·
                    refine ⟨991470895435291057620041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2643922387827442820320109 991470895435291057620041)
                    ·
                      refine ⟨743603171576468293215031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 991470895435291057620041 743603171576468293215031)
                      ·
                        rfl

theorem cell23_1448162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_1448162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1448162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1448162 prefixEnd_1448162 := by exact prefixLift 1448162
  have htrace : WordTrace (prefixWord ++ tailWord_1448162) baseStart_1448162 baseEnd_1448162 := by
    simpa [prefixWord, tailWord_1448162, baseEnd_1448162] using wordTrace_append hprefix tailTrace_1448162
  have hstable : (prefixWord ++ tailWord_1448162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448162).length < 2 ^ (prefixWord ++ tailWord_1448162).sum := by decide
  have hdescent : baseEnd_1448162 < baseStart_1448162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448177 : List Nat := [1, 2, 2, 2, 2, 1, 2, 4, 2, 5]
def baseStart_1448177 : Nat := 118140960795 + 1448177 * 2 ^ 59
def prefixEnd_1448177 : Nat := 4983230072969 + 3 ^ 40 * 1448177 * 2
def baseEnd_1448177 : Nat := 247870291262095244842487

theorem tailTrace_1448177 : CollatzResearch.WordTrace tailWord_1448177 prefixEnd_1448177 247870291262095244842487 := by
  unfold tailWord_1448177
  simp only [CollatzResearch.WordTrace]
  refine ⟨52819354474509532785846785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35212902983006355190564523 52819354474509532785846785)
  ·
    refine ⟨39614515855882149589385089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52819354474509532785846785 39614515855882149589385089)
    ·
      refine ⟨29710886891911612192038817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39614515855882149589385089 29710886891911612192038817)
      ·
        refine ⟨22283165168933709144029113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29710886891911612192038817 22283165168933709144029113)
        ·
          refine ⟨16712373876700281858021835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22283165168933709144029113 16712373876700281858021835)
          ·
            refine ⟨25068560815050422787032753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16712373876700281858021835 25068560815050422787032753)
            ·
              refine ⟨18801420611287817090274565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25068560815050422787032753 18801420611287817090274565)
              ·
                refine ⟨3525266364616465704426481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18801420611287817090274565 3525266364616465704426481)
                ·
                  refine ⟨2643949773462349278319861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3525266364616465704426481 2643949773462349278319861)
                  ·
                    refine ⟨247870291262095244842487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2643949773462349278319861 247870291262095244842487)
                    ·
                      rfl

theorem cell23_1448177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 4, 2, 5].length) (baseStart_1448177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1448177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1448177 prefixEnd_1448177 := by exact prefixLift 1448177
  have htrace : WordTrace (prefixWord ++ tailWord_1448177) baseStart_1448177 baseEnd_1448177 := by
    simpa [prefixWord, tailWord_1448177, baseEnd_1448177] using wordTrace_append hprefix tailTrace_1448177
  have hstable : (prefixWord ++ tailWord_1448177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448177).length < 2 ^ (prefixWord ++ tailWord_1448177).sum := by decide
  have hdescent : baseEnd_1448177 < baseStart_1448177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448194 : List Nat := [3, 4, 1, 1, 2, 1, 1, 2, 1, 7]
def baseStart_1448194 : Nat := 118140960795 + 1448194 * 2 ^ 59
def prefixEnd_1448194 : Nat := 4983230072969 + 3 ^ 40 * 1448194 * 2
def baseEnd_1448194 : Nat := 247873200985804056004961

theorem tailTrace_1448194 : CollatzResearch.WordTrace tailWord_1448194 prefixEnd_1448194 247873200985804056004961 := by
  unfold tailWord_1448194
  simp only [CollatzResearch.WordTrace]
  refine ⟨13204993628861986172303909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35213316343631963126143757 13204993628861986172303909)
  ·
    refine ⟨2475936305411622407306983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13204993628861986172303909 2475936305411622407306983)
    ·
      refine ⟨3713904458117433610960475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2475936305411622407306983 3713904458117433610960475)
      ·
        refine ⟨5570856687176150416440713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3713904458117433610960475 5570856687176150416440713)
        ·
          refine ⟨4178142515382112812330535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5570856687176150416440713 4178142515382112812330535)
          ·
            refine ⟨6267213773073169218495803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4178142515382112812330535 6267213773073169218495803)
            ·
              refine ⟨9400820659609753827743705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6267213773073169218495803 9400820659609753827743705)
              ·
                refine ⟨7050615494707315370807779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9400820659609753827743705 7050615494707315370807779)
                ·
                  refine ⟨10575923242060973056211669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7050615494707315370807779 10575923242060973056211669)
                  ·
                    refine ⟨247873200985804056004961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10575923242060973056211669 247873200985804056004961)
                    ·
                      rfl

theorem cell23_1448194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_1448194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1448194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1448194 prefixEnd_1448194 := by exact prefixLift 1448194
  have htrace : WordTrace (prefixWord ++ tailWord_1448194) baseStart_1448194 baseEnd_1448194 := by
    simpa [prefixWord, tailWord_1448194, baseEnd_1448194] using wordTrace_append hprefix tailTrace_1448194
  have hstable : (prefixWord ++ tailWord_1448194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448194).length < 2 ^ (prefixWord ++ tailWord_1448194).sum := by decide
  have hdescent : baseEnd_1448194 < baseStart_1448194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448197 : List Nat := [1, 3, 1, 1, 2, 1, 2, 1, 6, 1, 4]
def baseStart_1448197 : Nat := 118140960795 + 1448197 * 2 ^ 59
def prefixEnd_1448197 : Nat := 4983230072969 + 3 ^ 40 * 1448197 * 2
def baseEnd_1448197 : Nat := 743621143399375656277369

theorem tailTrace_1448197 : CollatzResearch.WordTrace tailWord_1448197 prefixEnd_1448197 743621143399375656277369 := by
  unfold tailWord_1448197
  simp only [CollatzResearch.WordTrace]
  refine ⟨52820083934437076201574845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35213389289624717467716563 52820083934437076201574845)
  ·
    refine ⟨19807531475413903575590567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52820083934437076201574845 19807531475413903575590567)
    ·
      refine ⟨29711297213120855363385851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19807531475413903575590567 29711297213120855363385851)
      ·
        refine ⟨44566945819681283045078777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29711297213120855363385851 44566945819681283045078777)
        ·
          refine ⟨33425209364760962283809083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44566945819681283045078777 33425209364760962283809083)
          ·
            refine ⟨50137814047141443425713625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33425209364760962283809083 50137814047141443425713625)
            ·
              refine ⟨37603360535356082569285219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50137814047141443425713625 37603360535356082569285219)
              ·
                refine ⟨56405040803034123853927829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37603360535356082569285219 56405040803034123853927829)
                ·
                  refine ⟨2643986287642224555652867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 56405040803034123853927829 2643986287642224555652867)
                  ·
                    refine ⟨3965979431463336833479301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2643986287642224555652867 3965979431463336833479301)
                    ·
                      refine ⟨743621143399375656277369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3965979431463336833479301 743621143399375656277369)
                      ·
                        rfl

theorem cell23_1448197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 6, 1, 4].length) (baseStart_1448197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1448197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1448197 prefixEnd_1448197 := by exact prefixLift 1448197
  have htrace : WordTrace (prefixWord ++ tailWord_1448197) baseStart_1448197 baseEnd_1448197 := by
    simpa [prefixWord, tailWord_1448197, baseEnd_1448197] using wordTrace_append hprefix tailTrace_1448197
  have hstable : (prefixWord ++ tailWord_1448197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448197).length < 2 ^ (prefixWord ++ tailWord_1448197).sum := by decide
  have hdescent : baseEnd_1448197 < baseStart_1448197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448291 : List Nat := [1, 1, 1, 5, 2, 1, 1, 4, 2, 3, 2]
def baseStart_1448291 : Nat := 118140960795 + 1448291 * 2 ^ 59
def prefixEnd_1448291 : Nat := 4983230072969 + 3 ^ 40 * 1448291 * 2
def baseEnd_1448291 : Nat := 743669410580898288501937

theorem tailTrace_1448291 : CollatzResearch.WordTrace tailWord_1448291 prefixEnd_1448291 743669410580898288501937 := by
  unfold tailWord_1448291
  simp only [CollatzResearch.WordTrace]
  refine ⟨52823512396096530255496727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35215674930731020170331151 52823512396096530255496727)
  ·
    refine ⟨79235268594144795383245091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52823512396096530255496727 79235268594144795383245091)
    ·
      refine ⟨118852902891217193074867637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79235268594144795383245091 118852902891217193074867637)
      ·
        refine ⟨11142459646051611850768841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 118852902891217193074867637 11142459646051611850768841)
        ·
          refine ⟨8356844734538708888076631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11142459646051611850768841 8356844734538708888076631)
          ·
            refine ⟨12535267101808063332114947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8356844734538708888076631 12535267101808063332114947)
            ·
              refine ⟨18802900652712094998172421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12535267101808063332114947 18802900652712094998172421)
              ·
                refine ⟨3525543872383517812157329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18802900652712094998172421 3525543872383517812157329)
                ·
                  refine ⟨2644157904287638359117997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3525543872383517812157329 2644157904287638359117997)
                  ·
                    refine ⟨991559214107864384669249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2644157904287638359117997 991559214107864384669249)
                    ·
                      refine ⟨743669410580898288501937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 991559214107864384669249 743669410580898288501937)
                      ·
                        rfl

theorem cell23_1448291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 4, 2, 3, 2].length) (baseStart_1448291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1448291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1448291 prefixEnd_1448291 := by exact prefixLift 1448291
  have htrace : WordTrace (prefixWord ++ tailWord_1448291) baseStart_1448291 baseEnd_1448291 := by
    simpa [prefixWord, tailWord_1448291, baseEnd_1448291] using wordTrace_append hprefix tailTrace_1448291
  have hstable : (prefixWord ++ tailWord_1448291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448291).length < 2 ^ (prefixWord ++ tailWord_1448291).sum := by decide
  have hdescent : baseEnd_1448291 < baseStart_1448291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448297 : List Nat := [1, 2, 1, 1, 1, 3, 3, 2, 3, 6]
def baseStart_1448297 : Nat := 118140960795 + 1448297 * 2 ^ 59
def prefixEnd_1448297 : Nat := 4983230072969 + 3 ^ 40 * 1448297 * 2
def baseEnd_1448297 : Nat := 247890830488275088342303

theorem tailTrace_1448297 : CollatzResearch.WordTrace tailWord_1448297 prefixEnd_1448297 247890830488275088342303 := by
  unfold tailWord_1448297
  simp only [CollatzResearch.WordTrace]
  refine ⟨52823731234074793280215145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35215820822716528853476763 52823731234074793280215145)
  ·
    refine ⟨39617798425556094960161359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52823731234074793280215145 39617798425556094960161359)
    ·
      refine ⟨59426697638334142440242039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39617798425556094960161359 59426697638334142440242039)
      ·
        refine ⟨89140046457501213660363059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59426697638334142440242039 89140046457501213660363059)
        ·
          refine ⟨133710069686251820490544589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89140046457501213660363059 133710069686251820490544589)
          ·
            refine ⟨50141276132344432683954221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133710069686251820490544589 50141276132344432683954221)
            ·
              refine ⟨18802978549629162256482833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50141276132344432683954221 18802978549629162256482833)
              ·
                refine ⟨14102233912221871692362125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18802978549629162256482833 14102233912221871692362125)
                ·
                  refine ⟨5288337717083201884635797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14102233912221871692362125 5288337717083201884635797)
                  ·
                    refine ⟨247890830488275088342303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5288337717083201884635797 247890830488275088342303)
                    ·
                      rfl

theorem cell23_1448297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 3, 6].length) (baseStart_1448297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1448297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1448297 prefixEnd_1448297 := by exact prefixLift 1448297
  have htrace : WordTrace (prefixWord ++ tailWord_1448297) baseStart_1448297 baseEnd_1448297 := by
    simpa [prefixWord, tailWord_1448297, baseEnd_1448297] using wordTrace_append hprefix tailTrace_1448297
  have hstable : (prefixWord ++ tailWord_1448297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448297).length < 2 ^ (prefixWord ++ tailWord_1448297).sum := by decide
  have hdescent : baseEnd_1448297 < baseStart_1448297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448304 : List Nat := [2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 4]
def baseStart_1448304 : Nat := 118140960795 + 1448304 * 2 ^ 59
def prefixEnd_1448304 : Nat := 4983230072969 + 3 ^ 40 * 1448304 * 2
def baseEnd_1448304 : Nat := 743676085829406737639377

theorem tailTrace_1448304 : CollatzResearch.WordTrace tailWord_1448304 prefixEnd_1448304 743676085829406737639377 := by
  unfold tailWord_1448304
  simp only [CollatzResearch.WordTrace]
  refine ⟨26411993272524716737859983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35215991030032955650479977 26411993272524716737859983)
  ·
    refine ⟨39617989908787075106789975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26411993272524716737859983 39617989908787075106789975)
    ·
      refine ⟨59426984863180612660184963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39617989908787075106789975 59426984863180612660184963)
      ·
        refine ⟨89140477294770918990277445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59426984863180612660184963 89140477294770918990277445)
        ·
          refine ⟨16713839492769547310677021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89140477294770918990277445 16713839492769547310677021)
          ·
            refine ⟨6267689809788580241503883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16713839492769547310677021 6267689809788580241503883)
            ·
              refine ⟨9401534714682870362255825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6267689809788580241503883 9401534714682870362255825)
              ·
                refine ⟨7051151036012152771691869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9401534714682870362255825 7051151036012152771691869)
                ·
                  refine ⟨2644181638504557289384451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7051151036012152771691869 2644181638504557289384451)
                  ·
                    refine ⟨3966272457756835934076677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2644181638504557289384451 3966272457756835934076677)
                    ·
                      refine ⟨743676085829406737639377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3966272457756835934076677 743676085829406737639377)
                      ·
                        rfl

theorem cell23_1448304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 4].length) (baseStart_1448304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1448304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1448304 prefixEnd_1448304 := by exact prefixLift 1448304
  have htrace : WordTrace (prefixWord ++ tailWord_1448304) baseStart_1448304 baseEnd_1448304 := by
    simpa [prefixWord, tailWord_1448304, baseEnd_1448304] using wordTrace_append hprefix tailTrace_1448304
  have hstable : (prefixWord ++ tailWord_1448304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448304).length < 2 ^ (prefixWord ++ tailWord_1448304).sum := by decide
  have hdescent : baseEnd_1448304 < baseStart_1448304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448321 : List Nat := [1, 2, 4, 3, 1, 1, 2, 1, 3, 1, 4]
def baseStart_1448321 : Nat := 118140960795 + 1448321 * 2 ^ 59
def prefixEnd_1448321 : Nat := 4983230072969 + 3 ^ 40 * 1448321 * 2
def baseEnd_1448321 : Nat := 743684815000533171126799

theorem tailTrace_1448321 : CollatzResearch.WordTrace tailWord_1448321 prefixEnd_1448321 743684815000533171126799 := by
  unfold tailWord_1448321
  simp only [CollatzResearch.WordTrace]
  refine ⟨52824606585987845379088817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35216404390658563586059211 52824606585987845379088817)
  ·
    refine ⟨39618454939490884034316613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52824606585987845379088817 39618454939490884034316613)
    ·
      refine ⟨7428460301154540756434365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39618454939490884034316613 7428460301154540756434365)
      ·
        refine ⟨2785672612932952783662887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7428460301154540756434365 2785672612932952783662887)
        ·
          refine ⟨4178508919399429175494331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2785672612932952783662887 4178508919399429175494331)
          ·
            refine ⟨6267763379099143763241497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4178508919399429175494331 6267763379099143763241497)
            ·
              refine ⟨4700822534324357822431123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6267763379099143763241497 4700822534324357822431123)
              ·
                refine ⟨7051233801486536733646685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4700822534324357822431123 7051233801486536733646685)
                ·
                  refine ⟨2644212675557451275117507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7051233801486536733646685 2644212675557451275117507)
                  ·
                    refine ⟨3966319013336176912676261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2644212675557451275117507 3966319013336176912676261)
                    ·
                      refine ⟨743684815000533171126799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3966319013336176912676261 743684815000533171126799)
                      ·
                        rfl

theorem cell23_1448321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_1448321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1448321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1448321 prefixEnd_1448321 := by exact prefixLift 1448321
  have htrace : WordTrace (prefixWord ++ tailWord_1448321) baseStart_1448321 baseEnd_1448321 := by
    simpa [prefixWord, tailWord_1448321, baseEnd_1448321] using wordTrace_append hprefix tailTrace_1448321
  have hstable : (prefixWord ++ tailWord_1448321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448321).length < 2 ^ (prefixWord ++ tailWord_1448321).sum := by decide
  have hdescent : baseEnd_1448321 < baseStart_1448321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448344 : List Nat := [2, 1, 2, 5, 1, 2, 10]
def baseStart_1448344 : Nat := 118140960795 + 1448344 * 2 ^ 59
def prefixEnd_1448344 : Nat := 4983230072969 + 3 ^ 40 * 1448344 * 2
def baseEnd_1448344 : Nat := 9181439815501068902953

theorem tailTrace_1448344 : CollatzResearch.WordTrace tailWord_1448344 prefixEnd_1448344 9181439815501068902953 := by
  unfold tailWord_1448344
  simp only [CollatzResearch.WordTrace]
  refine ⟨26412722732452260153588043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35216963643269680204784057 26412722732452260153588043)
  ·
    refine ⟨39619084098678390230382065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26412722732452260153588043 39619084098678390230382065)
    ·
      refine ⟨29714313074008792672786549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39619084098678390230382065 29714313074008792672786549)
      ·
        refine ⟨2785716850688324313073739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29714313074008792672786549 2785716850688324313073739)
        ·
          refine ⟨4178575276032486469610609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2785716850688324313073739 4178575276032486469610609)
          ·
            refine ⟨3133931457024364852207957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4178575276032486469610609 3133931457024364852207957)
            ·
              refine ⟨9181439815501068902953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3133931457024364852207957 9181439815501068902953)
              ·
                rfl

theorem cell23_1448344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 10].length) (baseStart_1448344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1448344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1448344 prefixEnd_1448344 := by exact prefixLift 1448344
  have htrace : WordTrace (prefixWord ++ tailWord_1448344) baseStart_1448344 baseEnd_1448344 := by
    simpa [prefixWord, tailWord_1448344, baseEnd_1448344] using wordTrace_append hprefix tailTrace_1448344
  have hstable : (prefixWord ++ tailWord_1448344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448344).length < 2 ^ (prefixWord ++ tailWord_1448344).sum := by decide
  have hdescent : baseEnd_1448344 < baseStart_1448344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448355 : List Nat := [1, 1, 1, 4, 1, 4, 2, 4, 1, 2, 2]
def baseStart_1448355 : Nat := 118140960795 + 1448355 * 2 ^ 59
def prefixEnd_1448355 : Nat := 4983230072969 + 3 ^ 40 * 1448355 * 2
def baseEnd_1448355 : Nat := 743702273342786038101643

theorem tailTrace_1448355 : CollatzResearch.WordTrace tailWord_1448355 prefixEnd_1448355 743702273342786038101643 := by
  unfold tailWord_1448355
  simp only [CollatzResearch.WordTrace]
  refine ⟨52825846667864669185826519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35217231111909779457217679 52825846667864669185826519)
  ·
    refine ⟨79238770001797003778739779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52825846667864669185826519 79238770001797003778739779)
    ·
      refine ⟨118858155002695505668109669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79238770001797003778739779 118858155002695505668109669)
      ·
        refine ⟨22285904063005407312770563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118858155002695505668109669 22285904063005407312770563)
        ·
          refine ⟨33428856094508110969155845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22285904063005407312770563 33428856094508110969155845)
          ·
            refine ⟨6267910517720270806716721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33428856094508110969155845 6267910517720270806716721)
            ·
              refine ⟨4700932888290203105037541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6267910517720270806716721 4700932888290203105037541)
              ·
                refine ⟨881424916554413082194539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4700932888290203105037541 881424916554413082194539)
                ·
                  refine ⟨1322137374831619623291809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 881424916554413082194539 1322137374831619623291809)
                  ·
                    refine ⟨991603031123714717468857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1322137374831619623291809 991603031123714717468857)
                    ·
                      refine ⟨743702273342786038101643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 991603031123714717468857 743702273342786038101643)
                      ·
                        rfl

theorem cell23_1448355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 4, 1, 2, 2].length) (baseStart_1448355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1448355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1448355 prefixEnd_1448355 := by exact prefixLift 1448355
  have htrace : WordTrace (prefixWord ++ tailWord_1448355) baseStart_1448355 baseEnd_1448355 := by
    simpa [prefixWord, tailWord_1448355, baseEnd_1448355] using wordTrace_append hprefix tailTrace_1448355
  have hstable : (prefixWord ++ tailWord_1448355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448355).length < 2 ^ (prefixWord ++ tailWord_1448355).sum := by decide
  have hdescent : baseEnd_1448355 < baseStart_1448355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448365 : List Nat := [1, 5, 2, 2, 3, 1, 1, 1, 1, 6]
def baseStart_1448365 : Nat := 118140960795 + 1448365 * 2 ^ 59
def prefixEnd_1448365 : Nat := 4983230072969 + 3 ^ 40 * 1448365 * 2
def baseEnd_1448365 : Nat := 247902469383110332992199

theorem tailTrace_1448365 : CollatzResearch.WordTrace tailWord_1448365 prefixEnd_1448365 247902469383110332992199 := by
  unfold tailWord_1448365
  simp only [CollatzResearch.WordTrace]
  refine ⟨52826211397828440893690549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35217474265218960595793699 52826211397828440893690549)
  ·
    refine ⟨4952457318546416333783489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52826211397828440893690549 4952457318546416333783489)
    ·
      refine ⟨3714342988909812250337617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4952457318546416333783489 3714342988909812250337617)
      ·
        refine ⟨2785757241682359187753213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3714342988909812250337617 2785757241682359187753213)
        ·
          refine ⟨1044658965630884695407455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2785757241682359187753213 1044658965630884695407455)
          ·
            refine ⟨1566988448446327043111183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1044658965630884695407455 1566988448446327043111183)
            ·
              refine ⟨2350482672669490564666775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1566988448446327043111183 2350482672669490564666775)
              ·
                refine ⟨3525724009004235847000163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2350482672669490564666775 3525724009004235847000163)
                ·
                  refine ⟨5288586013506353770500245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3525724009004235847000163 5288586013506353770500245)
                  ·
                    refine ⟨247902469383110332992199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5288586013506353770500245 247902469383110332992199)
                    ·
                      rfl

theorem cell23_1448365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_1448365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1448365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1448365 prefixEnd_1448365 := by exact prefixLift 1448365
  have htrace : WordTrace (prefixWord ++ tailWord_1448365) baseStart_1448365 baseEnd_1448365 := by
    simpa [prefixWord, tailWord_1448365, baseEnd_1448365] using wordTrace_append hprefix tailTrace_1448365
  have hstable : (prefixWord ++ tailWord_1448365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448365).length < 2 ^ (prefixWord ++ tailWord_1448365).sum := by decide
  have hdescent : baseEnd_1448365 < baseStart_1448365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448372 : List Nat := [2, 5, 2, 2, 1, 1, 2, 2, 1, 1, 4]
def baseStart_1448372 : Nat := 118140960795 + 1448372 * 2 ^ 59
def prefixEnd_1448372 : Nat := 4983230072969 + 3 ^ 40 * 1448372 * 2
def baseEnd_1448372 : Nat := 743711002513912471589065

theorem tailTrace_1448372 : CollatzResearch.WordTrace tailWord_1448372 prefixEnd_1448372 743711002513912471589065 := by
  unfold tailWord_1448372
  simp only [CollatzResearch.WordTrace]
  refine ⟨26413233354401540544597685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35217644472535387392796913 26413233354401540544597685)
  ·
    refine ⟨2476240626975144426056033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26413233354401540544597685 2476240626975144426056033)
    ·
      refine ⟨1857180470231358319542025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2476240626975144426056033 1857180470231358319542025)
      ·
        refine ⟨1392885352673518739656519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1857180470231358319542025 1392885352673518739656519)
        ·
          refine ⟨2089328029010278109484779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1392885352673518739656519 2089328029010278109484779)
          ·
            refine ⟨3133992043515417164227169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2089328029010278109484779 3133992043515417164227169)
            ·
              refine ⟨2350494032636562873170377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3133992043515417164227169 2350494032636562873170377)
              ·
                refine ⟨1762870524477422154877783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2350494032636562873170377 1762870524477422154877783)
                ·
                  refine ⟨2644305786716133232316675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1762870524477422154877783 2644305786716133232316675)
                  ·
                    refine ⟨3966458680074199848475013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2644305786716133232316675 3966458680074199848475013)
                    ·
                      refine ⟨743711002513912471589065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3966458680074199848475013 743711002513912471589065)
                      ·
                        rfl

theorem cell23_1448372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_1448372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1448372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1448372 prefixEnd_1448372 := by exact prefixLift 1448372
  have htrace : WordTrace (prefixWord ++ tailWord_1448372) baseStart_1448372 baseEnd_1448372 := by
    simpa [prefixWord, tailWord_1448372, baseEnd_1448372] using wordTrace_append hprefix tailTrace_1448372
  have hstable : (prefixWord ++ tailWord_1448372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448372).length < 2 ^ (prefixWord ++ tailWord_1448372).sum := by decide
  have hdescent : baseEnd_1448372 < baseStart_1448372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448451 : List Nat := [1, 1, 1, 3, 2, 1, 4, 5, 5]
def baseStart_1448451 : Nat := 118140960795 + 1448451 * 2 ^ 59
def prefixEnd_1448451 : Nat := 4983230072969 + 3 ^ 40 * 1448451 * 2
def baseEnd_1448451 : Nat := 82639063053957518055689

theorem tailTrace_1448451 : CollatzResearch.WordTrace tailWord_1448451 prefixEnd_1448451 82639063053957518055689 := by
  unfold tailWord_1448451
  simp only [CollatzResearch.WordTrace]
  refine ⟨52829348075516877581321207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35219565383677918387547471 52829348075516877581321207)
  ·
    refine ⟨79244022113275316371981811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52829348075516877581321207 79244022113275316371981811)
    ·
      refine ⟨118866033169912974557972717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79244022113275316371981811 118866033169912974557972717)
      ·
        refine ⟨44574762438717365459239769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118866033169912974557972717 44574762438717365459239769)
        ·
          refine ⟨33431071829038024094429827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44574762438717365459239769 33431071829038024094429827)
          ·
            refine ⟨50146607743557036141644741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33431071829038024094429827 50146607743557036141644741)
            ·
              refine ⟨9402488951916944276558389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50146607743557036141644741 9402488951916944276558389)
              ·
                refine ⟨881483339242213525927349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9402488951916944276558389 881483339242213525927349)
                ·
                  refine ⟨82639063053957518055689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 881483339242213525927349 82639063053957518055689)
                  ·
                    rfl

theorem cell23_1448451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 5, 5].length) (baseStart_1448451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1448451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1448451 prefixEnd_1448451 := by exact prefixLift 1448451
  have htrace : WordTrace (prefixWord ++ tailWord_1448451) baseStart_1448451 baseEnd_1448451 := by
    simpa [prefixWord, tailWord_1448451, baseEnd_1448451] using wordTrace_append hprefix tailTrace_1448451
  have hstable : (prefixWord ++ tailWord_1448451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448451).length < 2 ^ (prefixWord ++ tailWord_1448451).sum := by decide
  have hdescent : baseEnd_1448451 < baseStart_1448451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448462 : List Nat := [4, 1, 1, 2, 3, 2, 2, 2, 2, 2, 2]
def baseStart_1448462 : Nat := 118140960795 + 1448462 * 2 ^ 59
def prefixEnd_1448462 : Nat := 4983230072969 + 3 ^ 40 * 1448462 * 2
def baseEnd_1448462 : Nat := 743757215772817119463651

theorem tailTrace_1448462 : CollatzResearch.WordTrace tailWord_1448462 prefixEnd_1448462 743757215772817119463651 := by
  unfold tailWord_1448462
  simp only [CollatzResearch.WordTrace]
  refine ⟨6603718659809628307496455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35219832852318017639981093 6603718659809628307496455)
  ·
    refine ⟨9905577989714442461244683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6603718659809628307496455 9905577989714442461244683)
    ·
      refine ⟨14858366984571663691867025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9905577989714442461244683 14858366984571663691867025)
      ·
        refine ⟨11143775238428747768900269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14858366984571663691867025 11143775238428747768900269)
        ·
          refine ⟨4178915714410780413337601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11143775238428747768900269 4178915714410780413337601)
          ·
            refine ⟨3134186785808085310003201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4178915714410780413337601 3134186785808085310003201)
            ·
              refine ⟨2350640089356063982502401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3134186785808085310003201 2350640089356063982502401)
              ·
                refine ⟨1762980067017047986876801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2350640089356063982502401 1762980067017047986876801)
                ·
                  refine ⟨1322235050262785990157601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1762980067017047986876801 1322235050262785990157601)
                  ·
                    refine ⟨991676287697089492618201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1322235050262785990157601 991676287697089492618201)
                    ·
                      refine ⟨743757215772817119463651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 991676287697089492618201 743757215772817119463651)
                      ·
                        rfl

theorem cell23_1448462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 2, 2, 2, 2].length) (baseStart_1448462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1448462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1448462 prefixEnd_1448462 := by exact prefixLift 1448462
  have htrace : WordTrace (prefixWord ++ tailWord_1448462) baseStart_1448462 baseEnd_1448462 := by
    simpa [prefixWord, tailWord_1448462, baseEnd_1448462] using wordTrace_append hprefix tailTrace_1448462
  have hstable : (prefixWord ++ tailWord_1448462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448462).length < 2 ^ (prefixWord ++ tailWord_1448462).sum := by decide
  have hdescent : baseEnd_1448462 < baseStart_1448462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448464 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 8, 5]
def baseStart_1448464 : Nat := 118140960795 + 1448464 * 2 ^ 59
def prefixEnd_1448464 : Nat := 4983230072969 + 3 ^ 40 * 1448464 * 2
def baseEnd_1448464 : Nat := 247919414244708703879547

theorem tailTrace_1448464 : CollatzResearch.WordTrace tailWord_1448464 prefixEnd_1448464 247919414244708703879547 := by
  unfold tailWord_1448464
  simp only [CollatzResearch.WordTrace]
  refine ⟨26414911112234890400772223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35219881482979853867696297 26414911112234890400772223)
  ·
    refine ⟨39622366668352335601158335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26414911112234890400772223 39622366668352335601158335)
    ·
      refine ⟨59433550002528503401737503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39622366668352335601158335 59433550002528503401737503)
      ·
        refine ⟨89150325003792755102606255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59433550002528503401737503 89150325003792755102606255)
        ·
          refine ⟨133725487505689132653909383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89150325003792755102606255 133725487505689132653909383)
          ·
            refine ⟨200588231258533698980864075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133725487505689132653909383 200588231258533698980864075)
            ·
              refine ⟨300882346887800548471296113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 200588231258533698980864075 300882346887800548471296113)
              ·
                refine ⟨225661760165850411353472085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 300882346887800548471296113 225661760165850411353472085)
                ·
                  refine ⟨2644473751943559508048501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 225661760165850411353472085 2644473751943559508048501)
                  ·
                    refine ⟨247919414244708703879547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2644473751943559508048501 247919414244708703879547)
                    ·
                      rfl

theorem cell23_1448464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 8, 5].length) (baseStart_1448464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1448464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1448464 prefixEnd_1448464 := by exact prefixLift 1448464
  have htrace : WordTrace (prefixWord ++ tailWord_1448464) baseStart_1448464 baseEnd_1448464 := by
    simpa [prefixWord, tailWord_1448464, baseEnd_1448464] using wordTrace_append hprefix tailTrace_1448464
  have hstable : (prefixWord ++ tailWord_1448464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448464).length < 2 ^ (prefixWord ++ tailWord_1448464).sum := by decide
  have hdescent : baseEnd_1448464 < baseStart_1448464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448501 : List Nat := [1, 3, 3, 1, 1, 2, 3, 1, 1, 3, 4]
def baseStart_1448501 : Nat := 118140960795 + 1448501 * 2 ^ 59
def prefixEnd_1448501 : Nat := 4983230072969 + 3 ^ 40 * 1448501 * 2
def baseEnd_1448501 : Nat := 743777241518342466875971

theorem tailTrace_1448501 : CollatzResearch.WordTrace tailWord_1448501 prefixEnd_1448501 743777241518342466875971 := by
  unfold tailWord_1448501
  simp only [CollatzResearch.WordTrace]
  refine ⟨52831171725335736120641357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35220781150223824080427571 52831171725335736120641357)
  ·
    refine ⟨19811689397000901045240509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52831171725335736120641357 19811689397000901045240509)
    ·
      refine ⟨7429383523875337891965191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19811689397000901045240509 7429383523875337891965191)
      ·
        refine ⟨11144075285813006837947787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7429383523875337891965191 11144075285813006837947787)
        ·
          refine ⟨16716112928719510256921681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11144075285813006837947787 16716112928719510256921681)
          ·
            refine ⟨12537084696539632692691261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16716112928719510256921681 12537084696539632692691261)
            ·
              refine ⟨4701406761202362259759223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12537084696539632692691261 4701406761202362259759223)
              ·
                refine ⟨7052110141803543389638835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4701406761202362259759223 7052110141803543389638835)
                ·
                  refine ⟨10578165212705315084458253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7052110141803543389638835 10578165212705315084458253)
                  ·
                    refine ⟨3966811954764493156671845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10578165212705315084458253 3966811954764493156671845)
                    ·
                      refine ⟨743777241518342466875971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3966811954764493156671845 743777241518342466875971)
                      ·
                        rfl

theorem cell23_1448501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_1448501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1448501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1448501 prefixEnd_1448501 := by exact prefixLift 1448501
  have htrace : WordTrace (prefixWord ++ tailWord_1448501) baseStart_1448501 baseEnd_1448501 := by
    simpa [prefixWord, tailWord_1448501, baseEnd_1448501] using wordTrace_append hprefix tailTrace_1448501
  have hstable : (prefixWord ++ tailWord_1448501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448501).length < 2 ^ (prefixWord ++ tailWord_1448501).sum := by decide
  have hdescent : baseEnd_1448501 < baseStart_1448501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448511 : List Nat := [1, 1, 2, 2, 3, 2, 1, 2, 5, 4]
def baseStart_1448511 : Nat := 118140960795 + 1448511 * 2 ^ 59
def prefixEnd_1448511 : Nat := 4983230072969 + 3 ^ 40 * 1448511 * 2
def baseEnd_1448511 : Nat := 247927458774962475916975

theorem tailTrace_1448511 : CollatzResearch.WordTrace tailWord_1448511 prefixEnd_1448511 247927458774962475916975 := by
  unfold tailWord_1448511
  simp only [CollatzResearch.WordTrace]
  refine ⟨52831536455299507828505387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35221024303533005219003591 52831536455299507828505387)
  ·
    refine ⟨79247304682949261742758081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52831536455299507828505387 79247304682949261742758081)
    ·
      refine ⟨59435478512211946307068561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79247304682949261742758081 59435478512211946307068561)
      ·
        refine ⟨44576608884158959730301421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59435478512211946307068561 44576608884158959730301421)
        ·
          refine ⟨16716228331559609898863033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44576608884158959730301421 16716228331559609898863033)
          ·
            refine ⟨12537171248669707424147275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16716228331559609898863033 12537171248669707424147275)
            ·
              refine ⟨18805756873004561136220913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12537171248669707424147275 18805756873004561136220913)
              ·
                refine ⟨14104317654753420852165685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18805756873004561136220913 14104317654753420852165685)
                ·
                  refine ⟨1322279780133133204890533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14104317654753420852165685 1322279780133133204890533)
                  ·
                    refine ⟨247927458774962475916975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1322279780133133204890533 247927458774962475916975)
                    ·
                      rfl

theorem cell23_1448511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 5, 4].length) (baseStart_1448511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1448511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1448511 prefixEnd_1448511 := by exact prefixLift 1448511
  have htrace : WordTrace (prefixWord ++ tailWord_1448511) baseStart_1448511 baseEnd_1448511 := by
    simpa [prefixWord, tailWord_1448511, baseEnd_1448511] using wordTrace_append hprefix tailTrace_1448511
  have hstable : (prefixWord ++ tailWord_1448511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448511).length < 2 ^ (prefixWord ++ tailWord_1448511).sum := by decide
  have hdescent : baseEnd_1448511 < baseStart_1448511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448551 : List Nat := [1, 1, 5, 1, 1, 1, 1, 1, 1, 7, 3]
def baseStart_1448551 : Nat := 118140960795 + 1448551 * 2 ^ 59
def prefixEnd_1448551 : Nat := 4983230072969 + 3 ^ 40 * 1448551 * 2
def baseEnd_1448551 : Nat := 743802915551067271250741

theorem tailTrace_1448551 : CollatzResearch.WordTrace tailWord_1448551 prefixEnd_1448551 743802915551067271250741 := by
  unfold tailWord_1448551
  simp only [CollatzResearch.WordTrace]
  refine ⟨52832995375154594659961507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35221996916769729773307671 52832995375154594659961507)
  ·
    refine ⟨79249493062731891989942261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52832995375154594659961507 79249493062731891989942261)
    ·
      refine ⟨7429639974631114874057087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 79249493062731891989942261 7429639974631114874057087)
      ·
        refine ⟨11144459961946672311085631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7429639974631114874057087 11144459961946672311085631)
        ·
          refine ⟨16716689942920008466628447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11144459961946672311085631 16716689942920008466628447)
          ·
            refine ⟨25075034914380012699942671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16716689942920008466628447 25075034914380012699942671)
            ·
              refine ⟨37612552371570019049914007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25075034914380012699942671 37612552371570019049914007)
              ·
                refine ⟨56418828557355028574871011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37612552371570019049914007 56418828557355028574871011)
                ·
                  refine ⟨84628242836032542862306517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56418828557355028574871011 84628242836032542862306517)
                  ·
                    refine ⟨1983474441469512723335309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 84628242836032542862306517 1983474441469512723335309)
                    ·
                      refine ⟨743802915551067271250741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1983474441469512723335309 743802915551067271250741)
                      ·
                        rfl

theorem cell23_1448551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 7, 3].length) (baseStart_1448551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1448551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1448551 prefixEnd_1448551 := by exact prefixLift 1448551
  have htrace : WordTrace (prefixWord ++ tailWord_1448551) baseStart_1448551 baseEnd_1448551 := by
    simpa [prefixWord, tailWord_1448551, baseEnd_1448551] using wordTrace_append hprefix tailTrace_1448551
  have hstable : (prefixWord ++ tailWord_1448551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448551).length < 2 ^ (prefixWord ++ tailWord_1448551).sum := by decide
  have hdescent : baseEnd_1448551 < baseStart_1448551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448591 : List Nat := [1, 1, 2, 1, 1, 1, 1, 5, 5, 1, 4]
def baseStart_1448591 : Nat := 118140960795 + 1448591 * 2 ^ 59
def prefixEnd_1448591 : Nat := 4983230072969 + 3 ^ 40 * 1448591 * 2
def baseEnd_1448591 : Nat := 743823454777247114750557

theorem tailTrace_1448591 : CollatzResearch.WordTrace tailWord_1448591 prefixEnd_1448591 743823454777247114750557 := by
  unfold tailWord_1448591
  simp only [CollatzResearch.WordTrace]
  refine ⟨52834454295009681491417627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35222969530006454327611751 52834454295009681491417627)
  ·
    refine ⟨79251681442514522237126441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52834454295009681491417627 79251681442514522237126441)
    ·
      refine ⟨59438761081885891677844831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79251681442514522237126441 59438761081885891677844831)
      ·
        refine ⟨89158141622828837516767247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59438761081885891677844831 89158141622828837516767247)
        ·
          refine ⟨133737212434243256275150871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89158141622828837516767247 133737212434243256275150871)
          ·
            refine ⟨200605818651364884412726307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133737212434243256275150871 200605818651364884412726307)
            ·
              refine ⟨300908727977047326619089461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 200605818651364884412726307 300908727977047326619089461)
              ·
                refine ⟨28210193247848186870539637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 300908727977047326619089461 28210193247848186870539637)
                ·
                  refine ⟨2644705616985767519113091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28210193247848186870539637 2644705616985767519113091)
                  ·
                    refine ⟨3967058425478651278669637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2644705616985767519113091 3967058425478651278669637)
                    ·
                      refine ⟨743823454777247114750557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3967058425478651278669637 743823454777247114750557)
                      ·
                        rfl

theorem cell23_1448591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 5, 1, 4].length) (baseStart_1448591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1448591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1448591 prefixEnd_1448591 := by exact prefixLift 1448591
  have htrace : WordTrace (prefixWord ++ tailWord_1448591) baseStart_1448591 baseEnd_1448591 := by
    simpa [prefixWord, tailWord_1448591, baseEnd_1448591] using wordTrace_append hprefix tailTrace_1448591
  have hstable : (prefixWord ++ tailWord_1448591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448591).length < 2 ^ (prefixWord ++ tailWord_1448591).sum := by decide
  have hdescent : baseEnd_1448591 < baseStart_1448591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448601 : List Nat := [1, 2, 1, 2, 1, 2, 4, 3, 1, 6]
def baseStart_1448601 : Nat := 118140960795 + 1448601 * 2 ^ 59
def prefixEnd_1448601 : Nat := 4983230072969 + 3 ^ 40 * 1448601 * 2
def baseEnd_1448601 : Nat := 247942863194597358541837

theorem tailTrace_1448601 : CollatzResearch.WordTrace tailWord_1448601 prefixEnd_1448601 247942863194597358541837 := by
  unfold tailWord_1448601
  simp only [CollatzResearch.WordTrace]
  refine ⟨52834819024973453199281657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35223212683315635466187771 52834819024973453199281657)
  ·
    refine ⟨39626114268730089899461243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52834819024973453199281657 39626114268730089899461243)
    ·
      refine ⟨59439171403095134849191865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39626114268730089899461243 59439171403095134849191865)
      ·
        refine ⟨44579378552321351136893899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59439171403095134849191865 44579378552321351136893899)
        ·
          refine ⟨66869067828482026705340849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44579378552321351136893899 66869067828482026705340849)
          ·
            refine ⟨50151800871361520029005637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66869067828482026705340849 50151800871361520029005637)
            ·
              refine ⟨9403462663380285005438557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50151800871361520029005637 9403462663380285005438557)
              ·
                refine ⟨3526298498767606877039459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9403462663380285005438557 3526298498767606877039459)
                ·
                  refine ⟨5289447748151410315559189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3526298498767606877039459 5289447748151410315559189)
                  ·
                    refine ⟨247942863194597358541837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5289447748151410315559189 247942863194597358541837)
                    ·
                      rfl

theorem cell23_1448601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 3, 1, 6].length) (baseStart_1448601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1448601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1448601 prefixEnd_1448601 := by exact prefixLift 1448601
  have htrace : WordTrace (prefixWord ++ tailWord_1448601) baseStart_1448601 baseEnd_1448601 := by
    simpa [prefixWord, tailWord_1448601, baseEnd_1448601] using wordTrace_append hprefix tailTrace_1448601
  have hstable : (prefixWord ++ tailWord_1448601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448601).length < 2 ^ (prefixWord ++ tailWord_1448601).sum := by decide
  have hdescent : baseEnd_1448601 < baseStart_1448601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448631 : List Nat := [1, 1, 3, 1, 6, 11]
def baseStart_1448631 : Nat := 118140960795 + 1448631 * 2 ^ 59
def prefixEnd_1448631 : Nat := 4983230072969 + 3 ^ 40 * 1448631 * 2
def baseEnd_1448631 : Nat := 3061086395075831103911

theorem tailTrace_1448631 : CollatzResearch.WordTrace tailWord_1448631 prefixEnd_1448631 3061086395075831103911 := by
  unfold tailWord_1448631
  simp only [CollatzResearch.WordTrace]
  refine ⟨52835913214864768322873747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35223942143243178881915831 52835913214864768322873747)
  ·
    refine ⟨79253869822297152484310621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52835913214864768322873747 79253869822297152484310621)
    ·
      refine ⟨29720201183361432181616483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79253869822297152484310621 29720201183361432181616483)
      ·
        refine ⟨44580301775042148272424725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29720201183361432181616483 44580301775042148272424725)
        ·
          refine ⟨2089701645705100700269909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 44580301775042148272424725 2089701645705100700269909)
          ·
            refine ⟨3061086395075831103911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 2089701645705100700269909 3061086395075831103911)
            ·
              rfl

theorem cell23_1448631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 11].length) (baseStart_1448631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1448631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1448631 prefixEnd_1448631 := by exact prefixLift 1448631
  have htrace : WordTrace (prefixWord ++ tailWord_1448631) baseStart_1448631 baseEnd_1448631 := by
    simpa [prefixWord, tailWord_1448631, baseEnd_1448631] using wordTrace_append hprefix tailTrace_1448631
  have hstable : (prefixWord ++ tailWord_1448631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448631).length < 2 ^ (prefixWord ++ tailWord_1448631).sum := by decide
  have hdescent : baseEnd_1448631 < baseStart_1448631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448638 : List Nat := [4, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4]
def baseStart_1448638 : Nat := 118140960795 + 1448638 * 2 ^ 59
def prefixEnd_1448638 : Nat := 4983230072969 + 3 ^ 40 * 1448638 * 2
def baseEnd_1448638 : Nat := 743847588368008430862841

theorem tailTrace_1448638 : CollatzResearch.WordTrace tailWord_1448638 prefixEnd_1448638 743847588368008430862841 := by
  unfold tailWord_1448638
  simp only [CollatzResearch.WordTrace]
  refine ⟨6604521065729926064797321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35224112350559605678919045 6604521065729926064797321)
  ·
    refine ⟨4953390799297444548597991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6604521065729926064797321 4953390799297444548597991)
    ·
      refine ⟨7430086198946166822896987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4953390799297444548597991 7430086198946166822896987)
      ·
        refine ⟨11145129298419250234345481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7430086198946166822896987 11145129298419250234345481)
        ·
          refine ⟨8358846973814437675759111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11145129298419250234345481 8358846973814437675759111)
          ·
            refine ⟨12538270460721656513638667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8358846973814437675759111 12538270460721656513638667)
            ·
              refine ⟨18807405691082484770458001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12538270460721656513638667 18807405691082484770458001)
              ·
                refine ⟨14105554268311863577843501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18807405691082484770458001 14105554268311863577843501)
                ·
                  refine ⟨5289582850616948841691313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14105554268311863577843501 5289582850616948841691313)
                  ·
                    refine ⟨3967187137962711631268485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5289582850616948841691313 3967187137962711631268485)
                    ·
                      refine ⟨743847588368008430862841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3967187137962711631268485 743847588368008430862841)
                      ·
                        rfl

theorem cell23_1448638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_1448638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1448638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1448638 prefixEnd_1448638 := by exact prefixLift 1448638
  have htrace : WordTrace (prefixWord ++ tailWord_1448638) baseStart_1448638 baseEnd_1448638 := by
    simpa [prefixWord, tailWord_1448638, baseEnd_1448638] using wordTrace_append hprefix tailTrace_1448638
  have hstable : (prefixWord ++ tailWord_1448638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448638).length < 2 ^ (prefixWord ++ tailWord_1448638).sum := by decide
  have hdescent : baseEnd_1448638 < baseStart_1448638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448648 : List Nat := [2, 1, 3, 1, 2, 5, 1, 8]
def baseStart_1448648 : Nat := 118140960795 + 1448648 * 2 ^ 59
def prefixEnd_1448648 : Nat := 4983230072969 + 3 ^ 40 * 1448648 * 2
def baseEnd_1448648 : Nat := 27550100858316792286585

theorem tailTrace_1448648 : CollatzResearch.WordTrace tailWord_1448648 prefixEnd_1448648 27550100858316792286585 := by
  unfold tailWord_1448648
  simp only [CollatzResearch.WordTrace]
  refine ⟨26418266627901590113121299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35224355503868786817495065 26418266627901590113121299)
  ·
    refine ⟨39627399941852385169681949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26418266627901590113121299 39627399941852385169681949)
    ·
      refine ⟨14860274978194644438630731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39627399941852385169681949 14860274978194644438630731)
      ·
        refine ⟨22290412467291966657946097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14860274978194644438630731 22290412467291966657946097)
        ·
          refine ⟨16717809350468974993459573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22290412467291966657946097 16717809350468974993459573)
          ·
            refine ⟨1567294626606466405636835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16717809350468974993459573 1567294626606466405636835)
            ·
              refine ⟨2350941939909699608455253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1567294626606466405636835 2350941939909699608455253)
              ·
                refine ⟨27550100858316792286585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2350941939909699608455253 27550100858316792286585)
                ·
                  rfl

theorem cell23_1448648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 8].length) (baseStart_1448648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1448648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1448648 prefixEnd_1448648 := by exact prefixLift 1448648
  have htrace : WordTrace (prefixWord ++ tailWord_1448648) baseStart_1448648 baseEnd_1448648 := by
    simpa [prefixWord, tailWord_1448648, baseEnd_1448648] using wordTrace_append hprefix tailTrace_1448648
  have hstable : (prefixWord ++ tailWord_1448648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448648).length < 2 ^ (prefixWord ++ tailWord_1448648).sum := by decide
  have hdescent : baseEnd_1448648 < baseStart_1448648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448675 : List Nat := [1, 1, 1, 7, 1, 1, 2, 2, 1, 3, 3]
def baseStart_1448675 : Nat := 118140960795 + 1448675 * 2 ^ 59
def prefixEnd_1448675 : Nat := 4983230072969 + 3 ^ 40 * 1448675 * 2
def baseEnd_1448675 : Nat := 743866587152224786100171

theorem tailTrace_1448675 : CollatzResearch.WordTrace tailWord_1448675 prefixEnd_1448675 743866587152224786100171 := by
  unfold tailWord_1448675
  simp only [CollatzResearch.WordTrace]
  refine ⟨52837518026705363837475479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35225012017803575891650319 52837518026705363837475479)
  ·
    refine ⟨79256277040058045756213219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52837518026705363837475479 79256277040058045756213219)
    ·
      refine ⟨118884415560087068634319829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79256277040058045756213219 118884415560087068634319829)
      ·
        refine ⟨2786353489689540671116871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 118884415560087068634319829 2786353489689540671116871)
        ·
          refine ⟨4179530234534311006675307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2786353489689540671116871 4179530234534311006675307)
          ·
            refine ⟨6269295351801466510012961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4179530234534311006675307 6269295351801466510012961)
            ·
              refine ⟨4701971513851099882509721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6269295351801466510012961 4701971513851099882509721)
              ·
                refine ⟨3526478635388324911882291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4701971513851099882509721 3526478635388324911882291)
                ·
                  refine ⟨5289717953082487367823437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3526478635388324911882291 5289717953082487367823437)
                  ·
                    refine ⟨1983644232405932762933789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5289717953082487367823437 1983644232405932762933789)
                    ·
                      refine ⟨743866587152224786100171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1983644232405932762933789 743866587152224786100171)
                      ·
                        rfl

theorem cell23_1448675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_1448675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1448675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1448675 prefixEnd_1448675 := by exact prefixLift 1448675
  have htrace : WordTrace (prefixWord ++ tailWord_1448675) baseStart_1448675 baseEnd_1448675 := by
    simpa [prefixWord, tailWord_1448675, baseEnd_1448675] using wordTrace_append hprefix tailTrace_1448675
  have hstable : (prefixWord ++ tailWord_1448675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448675).length < 2 ^ (prefixWord ++ tailWord_1448675).sum := by decide
  have hdescent : baseEnd_1448675 < baseStart_1448675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448693 : List Nat := [1, 3, 6, 1, 1, 1, 2, 1, 3, 2, 2]
def baseStart_1448693 : Nat := 118140960795 + 1448693 * 2 ^ 59
def prefixEnd_1448693 : Nat := 4983230072969 + 3 ^ 40 * 1448693 * 2
def baseEnd_1448693 : Nat := 743875829804005715675089

theorem tailTrace_1448693 : CollatzResearch.WordTrace tailWord_1448693 prefixEnd_1448693 743875829804005715675089 := by
  unfold tailWord_1448693
  simp only [CollatzResearch.WordTrace]
  refine ⟨52838174540640152911630733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35225449693760101941087155 52838174540640152911630733)
  ·
    refine ⟨19814315452740057341861525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52838174540640152911630733 19814315452740057341861525)
    ·
      refine ⟨928796036847190187899759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 19814315452740057341861525 928796036847190187899759)
      ·
        refine ⟨1393194055270785281849639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 928796036847190187899759 1393194055270785281849639)
        ·
          refine ⟨2089791082906177922774459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1393194055270785281849639 2089791082906177922774459)
          ·
            refine ⟨3134686624359266884161689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2089791082906177922774459 3134686624359266884161689)
            ·
              refine ⟨2351014968269450163121267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3134686624359266884161689 2351014968269450163121267)
              ·
                refine ⟨3526522452404175244681901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2351014968269450163121267 3526522452404175244681901)
                ·
                  refine ⟨1322445919651565716755713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3526522452404175244681901 1322445919651565716755713)
                  ·
                    refine ⟨991834439738674287566785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1322445919651565716755713 991834439738674287566785)
                    ·
                      refine ⟨743875829804005715675089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 991834439738674287566785 743875829804005715675089)
                      ·
                        rfl

theorem cell23_1448693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_1448693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1448693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1448693 prefixEnd_1448693 := by exact prefixLift 1448693
  have htrace : WordTrace (prefixWord ++ tailWord_1448693) baseStart_1448693 baseEnd_1448693 := by
    simpa [prefixWord, tailWord_1448693, baseEnd_1448693] using wordTrace_append hprefix tailTrace_1448693
  have hstable : (prefixWord ++ tailWord_1448693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448693).length < 2 ^ (prefixWord ++ tailWord_1448693).sum := by decide
  have hdescent : baseEnd_1448693 < baseStart_1448693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448708 : List Nat := [2, 3, 2, 2, 1, 1, 1, 3, 2, 6]
def baseStart_1448708 : Nat := 118140960795 + 1448708 * 2 ^ 59
def prefixEnd_1448708 : Nat := 4983230072969 + 3 ^ 40 * 1448708 * 2
def baseEnd_1448708 : Nat := 247961177337941052329173

theorem tailTrace_1448708 : CollatzResearch.WordTrace tailWord_1448708 prefixEnd_1448708 247961177337941052329173 := by
  unfold tailWord_1448708
  simp only [CollatzResearch.WordTrace]
  refine ⟨26419360817792905236713389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35225814423723873648951185 26419360817792905236713389)
  ·
    refine ⟨9907260306672339463767521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26419360817792905236713389 9907260306672339463767521)
    ·
      refine ⟨7430445230004254597825641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9907260306672339463767521 7430445230004254597825641)
      ·
        refine ⟨5572833922503190948369231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7430445230004254597825641 5572833922503190948369231)
        ·
          refine ⟨8359250883754786422553847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5572833922503190948369231 8359250883754786422553847)
          ·
            refine ⟨12538876325632179633830771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8359250883754786422553847 12538876325632179633830771)
            ·
              refine ⟨18808314488448269450746157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12538876325632179633830771 18808314488448269450746157)
              ·
                refine ⟨7053117933168101044029809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18808314488448269450746157 7053117933168101044029809)
                ·
                  refine ⟨5289838449876075783022357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7053117933168101044029809 5289838449876075783022357)
                  ·
                    refine ⟨247961177337941052329173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5289838449876075783022357 247961177337941052329173)
                    ·
                      rfl

theorem cell23_1448708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_1448708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1448708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1448708 prefixEnd_1448708 := by exact prefixLift 1448708
  have htrace : WordTrace (prefixWord ++ tailWord_1448708) baseStart_1448708 baseEnd_1448708 := by
    simpa [prefixWord, tailWord_1448708, baseEnd_1448708] using wordTrace_append hprefix tailTrace_1448708
  have hstable : (prefixWord ++ tailWord_1448708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448708).length < 2 ^ (prefixWord ++ tailWord_1448708).sum := by decide
  have hdescent : baseEnd_1448708 < baseStart_1448708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448718 : List Nat := [4, 1, 1, 2, 1, 1, 1, 4, 2, 1, 5]
def baseStart_1448718 : Nat := 118140960795 + 1448718 * 2 ^ 59
def prefixEnd_1448718 : Nat := 4983230072969 + 3 ^ 40 * 1448718 * 2
def baseEnd_1448718 : Nat := 743888666820368117862473

theorem tailTrace_1448718 : CollatzResearch.WordTrace tailWord_1448718 prefixEnd_1448718 743888666820368117862473 := by
  unfold tailWord_1448718
  simp only [CollatzResearch.WordTrace]
  refine ⟨6604885795693697772661351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35226057577033054787527205 6604885795693697772661351)
  ·
    refine ⟨9907328693540546658992027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6604885795693697772661351 9907328693540546658992027)
    ·
      refine ⟨14860993040310819988488041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9907328693540546658992027 14860993040310819988488041)
      ·
        refine ⟨11145744780233114991366031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14860993040310819988488041 11145744780233114991366031)
        ·
          refine ⟨16718617170349672487049047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11145744780233114991366031 16718617170349672487049047)
          ·
            refine ⟨25077925755524508730573571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16718617170349672487049047 25077925755524508730573571)
            ·
              refine ⟨37616888633286763095860357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25077925755524508730573571 37616888633286763095860357)
              ·
                refine ⟨7053166618741268080473817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37616888633286763095860357 7053166618741268080473817)
                ·
                  refine ⟨5289874964055951060355363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7053166618741268080473817 5289874964055951060355363)
                  ·
                    refine ⟨7934812446083926590533045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5289874964055951060355363 7934812446083926590533045)
                    ·
                      refine ⟨743888666820368117862473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7934812446083926590533045 743888666820368117862473)
                      ·
                        rfl

theorem cell23_1448718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_1448718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1448718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1448718 prefixEnd_1448718 := by exact prefixLift 1448718
  have htrace : WordTrace (prefixWord ++ tailWord_1448718) baseStart_1448718 baseEnd_1448718 := by
    simpa [prefixWord, tailWord_1448718, baseEnd_1448718] using wordTrace_append hprefix tailTrace_1448718
  have hstable : (prefixWord ++ tailWord_1448718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448718).length < 2 ^ (prefixWord ++ tailWord_1448718).sum := by decide
  have hdescent : baseEnd_1448718 < baseStart_1448718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448731 : List Nat := [1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 7]
def baseStart_1448731 : Nat := 118140960795 + 1448731 * 2 ^ 59
def prefixEnd_1448731 : Nat := 4983230072969 + 3 ^ 40 * 1448731 * 2
def baseEnd_1448731 : Nat := 743895342068876566999913

theorem tailTrace_1448731 : CollatzResearch.WordTrace tailWord_1448731 prefixEnd_1448731 743895342068876566999913 := by
  unfold tailWord_1448731
  simp only [CollatzResearch.WordTrace]
  refine ⟨52839560514502485401514047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35226373676334990267676031 52839560514502485401514047)
  ·
    refine ⟨79259340771753728102271071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52839560514502485401514047 79259340771753728102271071)
    ·
      refine ⟨118889011157630592153406607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79259340771753728102271071 118889011157630592153406607)
      ·
        refine ⟨178333516736445888230109911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118889011157630592153406607 178333516736445888230109911)
        ·
          refine ⟨267500275104668832345164867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178333516736445888230109911 267500275104668832345164867)
          ·
            refine ⟨401250412657003248517747301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267500275104668832345164867 401250412657003248517747301)
            ·
              refine ⟨75234452373188109097077619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 401250412657003248517747301 75234452373188109097077619)
              ·
                refine ⟨112851678559782163645616429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75234452373188109097077619 112851678559782163645616429)
                ·
                  refine ⟨42319379459918311367106161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 112851678559782163645616429 42319379459918311367106161)
                  ·
                    refine ⟨31739534594938733525329621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42319379459918311367106161 31739534594938733525329621)
                    ·
                      refine ⟨743895342068876566999913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 31739534594938733525329621 743895342068876566999913)
                      ·
                        rfl

theorem cell23_1448731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 7].length) (baseStart_1448731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1448731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1448731 prefixEnd_1448731 := by exact prefixLift 1448731
  have htrace : WordTrace (prefixWord ++ tailWord_1448731) baseStart_1448731 baseEnd_1448731 := by
    simpa [prefixWord, tailWord_1448731, baseEnd_1448731] using wordTrace_append hprefix tailTrace_1448731
  have hstable : (prefixWord ++ tailWord_1448731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448731).length < 2 ^ (prefixWord ++ tailWord_1448731).sum := by decide
  have hdescent : baseEnd_1448731 < baseStart_1448731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448732 : List Nat := [2, 2, 3, 1, 1, 3, 1, 2, 4, 2, 2]
def baseStart_1448732 : Nat := 118140960795 + 1448732 * 2 ^ 59
def prefixEnd_1448732 : Nat := 4983230072969 + 3 ^ 40 * 1448732 * 2
def baseEnd_1448732 : Nat := 743895855549531063087409

theorem tailTrace_1448732 : CollatzResearch.WordTrace tailWord_1448732 prefixEnd_1448732 743895855549531063087409 := by
  unfold tailWord_1448732
  simp only [CollatzResearch.WordTrace]
  refine ⟨26419798493749431286150225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35226397991665908381533633 26419798493749431286150225)
  ·
    refine ⟨19814848870312073464612669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26419798493749431286150225 19814848870312073464612669)
    ·
      refine ⟨7430568326367027549229751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19814848870312073464612669 7430568326367027549229751)
      ·
        refine ⟨11145852489550541323844627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7430568326367027549229751 11145852489550541323844627)
        ·
          refine ⟨16718778734325811985766941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11145852489550541323844627 16718778734325811985766941)
          ·
            refine ⟨6269542025372179494662603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16718778734325811985766941 6269542025372179494662603)
            ·
              refine ⟨9404313038058269241993905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6269542025372179494662603 9404313038058269241993905)
              ·
                refine ⟨7053234778543701931495429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9404313038058269241993905 7053234778543701931495429)
                ·
                  refine ⟨1322481520976944112155393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7053234778543701931495429 1322481520976944112155393)
                  ·
                    refine ⟨991861140732708084116545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1322481520976944112155393 991861140732708084116545)
                    ·
                      refine ⟨743895855549531063087409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 991861140732708084116545 743895855549531063087409)
                      ·
                        rfl

theorem cell23_1448732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 4, 2, 2].length) (baseStart_1448732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1448732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1448732 prefixEnd_1448732 := by exact prefixLift 1448732
  have htrace : WordTrace (prefixWord ++ tailWord_1448732) baseStart_1448732 baseEnd_1448732 := by
    simpa [prefixWord, tailWord_1448732, baseEnd_1448732] using wordTrace_append hprefix tailTrace_1448732
  have hstable : (prefixWord ++ tailWord_1448732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448732).length < 2 ^ (prefixWord ++ tailWord_1448732).sum := by decide
  have hdescent : baseEnd_1448732 < baseStart_1448732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448755 : List Nat := [1, 1, 1, 2, 6, 3, 1, 1, 7]
def baseStart_1448755 : Nat := 118140960795 + 1448755 * 2 ^ 59
def prefixEnd_1448755 : Nat := 4983230072969 + 3 ^ 40 * 1448755 * 2
def baseEnd_1448755 : Nat := 82656407289398274788867

theorem tailTrace_1448755 : CollatzResearch.WordTrace tailWord_1448755 prefixEnd_1448755 82656407289398274788867 := by
  unfold tailWord_1448755
  simp only [CollatzResearch.WordTrace]
  refine ⟨52840435866415537500387719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35226957244277025000258479 52840435866415537500387719)
  ·
    refine ⟨79260653799623306250581579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52840435866415537500387719 79260653799623306250581579)
    ·
      refine ⟨118890980699434959375872369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79260653799623306250581579 118890980699434959375872369)
      ·
        refine ⟨89168235524576219531904277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118890980699434959375872369 89168235524576219531904277)
        ·
          refine ⟨4179761040214510290558013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 89168235524576219531904277 4179761040214510290558013)
          ·
            refine ⟨1567410390080441358959255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4179761040214510290558013 1567410390080441358959255)
            ·
              refine ⟨2351115585120662038438883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1567410390080441358959255 2351115585120662038438883)
              ·
                refine ⟨3526673377680993057658325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2351115585120662038438883 3526673377680993057658325)
                ·
                  refine ⟨82656407289398274788867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3526673377680993057658325 82656407289398274788867)
                  ·
                    rfl

theorem cell23_1448755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 1, 7].length) (baseStart_1448755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1448755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1448755 prefixEnd_1448755 := by exact prefixLift 1448755
  have htrace : WordTrace (prefixWord ++ tailWord_1448755) baseStart_1448755 baseEnd_1448755 := by
    simpa [prefixWord, tailWord_1448755, baseEnd_1448755] using wordTrace_append hprefix tailTrace_1448755
  have hstable : (prefixWord ++ tailWord_1448755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448755).length < 2 ^ (prefixWord ++ tailWord_1448755).sum := by decide
  have hdescent : baseEnd_1448755 < baseStart_1448755 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448766 : List Nat := [4, 2, 1, 2, 3, 1, 1, 3, 2, 2, 2]
def baseStart_1448766 : Nat := 118140960795 + 1448766 * 2 ^ 59
def prefixEnd_1448766 : Nat := 4983230072969 + 3 ^ 40 * 1448766 * 2
def baseEnd_1448766 : Nat := 743913313891783930062253

theorem tailTrace_1448766 : CollatzResearch.WordTrace tailWord_1448766 prefixEnd_1448766 743913313891783930062253 := by
  unfold tailWord_1448766
  simp only [CollatzResearch.WordTrace]
  refine ⟨6605104633671960797379769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35227224712917124252692101 6605104633671960797379769)
  ·
    refine ⟨4953828475253970598034827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6605104633671960797379769 4953828475253970598034827)
    ·
      refine ⟨7430742712880955897052241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4953828475253970598034827 7430742712880955897052241)
      ·
        refine ⟨5573057034660716922789181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7430742712880955897052241 5573057034660716922789181)
        ·
          refine ⟨2089896387997768846045943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5573057034660716922789181 2089896387997768846045943)
          ·
            refine ⟨3134844581996653269068915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2089896387997768846045943 3134844581996653269068915)
            ·
              refine ⟨4702266872994979903603373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3134844581996653269068915 4702266872994979903603373)
              ·
                refine ⟨1763350077373117463851265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4702266872994979903603373 1763350077373117463851265)
                ·
                  refine ⟨1322512558029838097888449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1763350077373117463851265 1322512558029838097888449)
                  ·
                    refine ⟨991884418522378573416337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1322512558029838097888449 991884418522378573416337)
                    ·
                      refine ⟨743913313891783930062253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 991884418522378573416337 743913313891783930062253)
                      ·
                        rfl

theorem cell23_1448766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 3, 2, 2, 2].length) (baseStart_1448766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1448766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1448766 prefixEnd_1448766 := by exact prefixLift 1448766
  have htrace : WordTrace (prefixWord ++ tailWord_1448766) baseStart_1448766 baseEnd_1448766 := by
    simpa [prefixWord, tailWord_1448766, baseEnd_1448766] using wordTrace_append hprefix tailTrace_1448766
  have hstable : (prefixWord ++ tailWord_1448766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448766).length < 2 ^ (prefixWord ++ tailWord_1448766).sum := by decide
  have hdescent : baseEnd_1448766 < baseStart_1448766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448805 : List Nat := [1, 3, 1, 3, 1, 1, 4, 2, 2, 1, 4]
def baseStart_1448805 : Nat := 118140960795 + 1448805 * 2 ^ 59
def prefixEnd_1448805 : Nat := 4983230072969 + 3 ^ 40 * 1448805 * 2
def baseEnd_1448805 : Nat := 743933339637309277474573

theorem tailTrace_1448805 : CollatzResearch.WordTrace tailWord_1448805 prefixEnd_1448805 743933339637309277474573 := by
  unfold tailWord_1448805
  simp only [CollatzResearch.WordTrace]
  refine ⟨52842259516234396039707869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35228173010822930693138579 52842259516234396039707869)
  ·
    refine ⟨19815847318587898514890451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52842259516234396039707869 19815847318587898514890451)
    ·
      refine ⟨29723770977881847772335677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19815847318587898514890451 29723770977881847772335677)
      ·
        refine ⟨11146414116705692914625879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29723770977881847772335677 11146414116705692914625879)
        ·
          refine ⟨16719621175058539371938819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11146414116705692914625879 16719621175058539371938819)
          ·
            refine ⟨25079431762587809057908229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16719621175058539371938819 25079431762587809057908229)
            ·
              refine ⟨4702393455485214198357793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25079431762587809057908229 4702393455485214198357793)
              ·
                refine ⟨3526795091613910648768345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4702393455485214198357793 3526795091613910648768345)
                ·
                  refine ⟨2645096318710432986576259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3526795091613910648768345 2645096318710432986576259)
                  ·
                    refine ⟨3967644478065649479864389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2645096318710432986576259 3967644478065649479864389)
                    ·
                      refine ⟨743933339637309277474573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3967644478065649479864389 743933339637309277474573)
                      ·
                        rfl

theorem cell23_1448805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_1448805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1448805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1448805 prefixEnd_1448805 := by exact prefixLift 1448805
  have htrace : WordTrace (prefixWord ++ tailWord_1448805) baseStart_1448805 baseEnd_1448805 := by
    simpa [prefixWord, tailWord_1448805, baseEnd_1448805] using wordTrace_append hprefix tailTrace_1448805
  have hstable : (prefixWord ++ tailWord_1448805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448805).length < 2 ^ (prefixWord ++ tailWord_1448805).sum := by decide
  have hdescent : baseEnd_1448805 < baseStart_1448805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448842 : List Nat := [3, 1, 2, 4, 1, 2, 1, 1, 1, 4, 3]
def baseStart_1448842 : Nat := 118140960795 + 1448842 * 2 ^ 59
def prefixEnd_1448842 : Nat := 4983230072969 + 3 ^ 40 * 1448842 * 2
def baseEnd_1448842 : Nat := 743952338421525632711903

theorem tailTrace_1448842 : CollatzResearch.WordTrace tailWord_1448842 prefixEnd_1448842 743952338421525632711903 := by
  unfold tailWord_1448842
  simp only [CollatzResearch.WordTrace]
  refine ⟨13210902254275087839701195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35229072678066900905869853 13210902254275087839701195)
  ·
    refine ⟨19816353381412631759551793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13210902254275087839701195 19816353381412631759551793)
    ·
      refine ⟨14862265036059473819663845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19816353381412631759551793 14862265036059473819663845)
      ·
        refine ⟨2786674694261151341186971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14862265036059473819663845 2786674694261151341186971)
        ·
          refine ⟨4180012041391727011780457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2786674694261151341186971 4180012041391727011780457)
          ·
            refine ⟨3135009031043795258835343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4180012041391727011780457 3135009031043795258835343)
            ·
              refine ⟨4702513546565692888253015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3135009031043795258835343 4702513546565692888253015)
              ·
                refine ⟨7053770319848539332379523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4702513546565692888253015 7053770319848539332379523)
                ·
                  refine ⟨10580655479772808998569285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7053770319848539332379523 10580655479772808998569285)
                  ·
                    refine ⟨1983872902457401687231741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10580655479772808998569285 1983872902457401687231741)
                    ·
                      refine ⟨743952338421525632711903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1983872902457401687231741 743952338421525632711903)
                      ·
                        rfl

theorem cell23_1448842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_1448842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1448842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1448842 prefixEnd_1448842 := by exact prefixLift 1448842
  have htrace : WordTrace (prefixWord ++ tailWord_1448842) baseStart_1448842 baseEnd_1448842 := by
    simpa [prefixWord, tailWord_1448842, baseEnd_1448842] using wordTrace_append hprefix tailTrace_1448842
  have hstable : (prefixWord ++ tailWord_1448842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448842).length < 2 ^ (prefixWord ++ tailWord_1448842).sum := by decide
  have hdescent : baseEnd_1448842 < baseStart_1448842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448865 : List Nat := [1, 2, 3, 4, 1, 1, 1, 1, 1, 2, 6]
def baseStart_1448865 : Nat := 118140960795 + 1448865 * 2 ^ 59
def prefixEnd_1448865 : Nat := 4983230072969 + 3 ^ 40 * 1448865 * 2
def baseEnd_1448865 : Nat := 743964148476579042724297

theorem tailTrace_1448865 : CollatzResearch.WordTrace tailWord_1448865 prefixEnd_1448865 743964148476579042724297 := by
  unfold tailWord_1448865
  simp only [CollatzResearch.WordTrace]
  refine ⟨52844447896017026286892049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35229631930678017524594699 52844447896017026286892049)
  ·
    refine ⟨39633335922012769715169037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52844447896017026286892049 39633335922012769715169037)
    ·
      refine ⟨14862500970754788643188389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39633335922012769715169037 14862500970754788643188389)
      ·
        refine ⟨2786718932016522870597823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14862500970754788643188389 2786718932016522870597823)
        ·
          refine ⟨4180078398024784305896735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2786718932016522870597823 4180078398024784305896735)
          ·
            refine ⟨6270117597037176458845103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4180078398024784305896735 6270117597037176458845103)
            ·
              refine ⟨9405176395555764688267655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6270117597037176458845103 9405176395555764688267655)
              ·
                refine ⟨14107764593333647032401483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9405176395555764688267655 14107764593333647032401483)
                ·
                  refine ⟨21161646890000470548602225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14107764593333647032401483 21161646890000470548602225)
                  ·
                    refine ⟨15871235167500352911451669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21161646890000470548602225 15871235167500352911451669)
                    ·
                      refine ⟨743964148476579042724297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15871235167500352911451669 743964148476579042724297)
                      ·
                        rfl

theorem cell23_1448865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_1448865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1448865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1448865 prefixEnd_1448865 := by exact prefixLift 1448865
  have htrace : WordTrace (prefixWord ++ tailWord_1448865) baseStart_1448865 baseEnd_1448865 := by
    simpa [prefixWord, tailWord_1448865, baseEnd_1448865] using wordTrace_append hprefix tailTrace_1448865
  have hstable : (prefixWord ++ tailWord_1448865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448865).length < 2 ^ (prefixWord ++ tailWord_1448865).sum := by decide
  have hdescent : baseEnd_1448865 < baseStart_1448865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448900 : List Nat := [2, 3, 3, 3, 2, 1, 1, 3, 1, 4]
def baseStart_1448900 : Nat := 118140960795 + 1448900 * 2 ^ 59
def prefixEnd_1448900 : Nat := 4983230072969 + 3 ^ 40 * 1448900 * 2
def baseEnd_1448900 : Nat := 247994040099828801928879

theorem tailTrace_1448900 : CollatzResearch.WordTrace tailWord_1448900 prefixEnd_1448900 247994040099828801928879 := by
  unfold tailWord_1448900
  simp only [CollatzResearch.WordTrace]
  refine ⟨26422862225445113632208077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35230482967260151509610769 26422862225445113632208077)
  ·
    refine ⟨9908573334541917612078029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26422862225445113632208077 9908573334541917612078029)
    ·
      refine ⟨3715715000453219104529261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9908573334541917612078029 3715715000453219104529261)
      ·
        refine ⟨1393393125169957164198473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3715715000453219104529261 1393393125169957164198473)
        ·
          refine ⟨1045044843877467873148855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1393393125169957164198473 1045044843877467873148855)
          ·
            refine ⟨1567567265816201809723283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1045044843877467873148855 1567567265816201809723283)
            ·
              refine ⟨2351350898724302714584925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1567567265816201809723283 2351350898724302714584925)
              ·
                refine ⟨881756587021613517969347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2351350898724302714584925 881756587021613517969347)
                ·
                  refine ⟨1322634880532420276954021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 881756587021613517969347 1322634880532420276954021)
                  ·
                    refine ⟨247994040099828801928879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1322634880532420276954021 247994040099828801928879)
                    ·
                      rfl

theorem cell23_1448900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_1448900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1448900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1448900 prefixEnd_1448900 := by exact prefixLift 1448900
  have htrace : WordTrace (prefixWord ++ tailWord_1448900) baseStart_1448900 baseEnd_1448900 := by
    simpa [prefixWord, tailWord_1448900, baseEnd_1448900] using wordTrace_append hprefix tailTrace_1448900
  have hstable : (prefixWord ++ tailWord_1448900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448900).length < 2 ^ (prefixWord ++ tailWord_1448900).sum := by decide
  have hdescent : baseEnd_1448900 < baseStart_1448900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448922 : List Nat := [3, 1, 1, 2, 4, 1, 2, 1, 4, 4]
def baseStart_1448922 : Nat := 118140960795 + 1448922 * 2 ^ 59
def prefixEnd_1448922 : Nat := 4983230072969 + 3 ^ 40 * 1448922 * 2
def baseEnd_1448922 : Nat := 247997805624628439903845

theorem tailTrace_1448922 : CollatzResearch.WordTrace tailWord_1448922 prefixEnd_1448922 247997805624628439903845 := by
  unfold tailWord_1448922
  simp only [CollatzResearch.WordTrace]
  refine ⟨13211631714202631255429255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35231017904540350014478013 13211631714202631255429255)
  ·
    refine ⟨19817447571303946883143883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13211631714202631255429255 19817447571303946883143883)
    ·
      refine ⟨29726171356955920324715825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19817447571303946883143883 29726171356955920324715825)
      ·
        refine ⟨22294628517716940243536869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29726171356955920324715825 22294628517716940243536869)
        ·
          refine ⟨4180242847071926295663163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22294628517716940243536869 4180242847071926295663163)
          ·
            refine ⟨6270364270607889443494745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4180242847071926295663163 6270364270607889443494745)
            ·
              refine ⟨4702773202955917082621059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6270364270607889443494745 4702773202955917082621059)
              ·
                refine ⟨7054159804433875623931589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4702773202955917082621059 7054159804433875623931589)
                ·
                  refine ⟨1322654963331351679487173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7054159804433875623931589 1322654963331351679487173)
                  ·
                    refine ⟨247997805624628439903845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1322654963331351679487173 247997805624628439903845)
                    ·
                      rfl

theorem cell23_1448922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 4, 4].length) (baseStart_1448922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1448922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1448922 prefixEnd_1448922 := by exact prefixLift 1448922
  have htrace : WordTrace (prefixWord ++ tailWord_1448922) baseStart_1448922 baseEnd_1448922 := by
    simpa [prefixWord, tailWord_1448922, baseEnd_1448922] using wordTrace_append hprefix tailTrace_1448922
  have hstable : (prefixWord ++ tailWord_1448922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448922).length < 2 ^ (prefixWord ++ tailWord_1448922).sum := by decide
  have hdescent : baseEnd_1448922 < baseStart_1448922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448935 : List Nat := [1, 1, 5, 2, 2, 1, 1, 10]
def baseStart_1448935 : Nat := 118140960795 + 1448935 * 2 ^ 59
def prefixEnd_1448935 : Nat := 4983230072969 + 3 ^ 40 * 1448935 * 2
def baseEnd_1448935 : Nat := 27555558967496065512925

theorem tailTrace_1448935 : CollatzResearch.WordTrace tailWord_1448935 prefixEnd_1448935 27555558967496065512925 := by
  unfold tailWord_1448935
  simp only [CollatzResearch.WordTrace]
  refine ⟨52847001005763428241940259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35231334003842285494626839 52847001005763428241940259)
  ·
    refine ⟨79270501508645142362910389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52847001005763428241940259 79270501508645142362910389)
    ·
      refine ⟨7431609516435482096522849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 79270501508645142362910389 7431609516435482096522849)
      ·
        refine ⟨5573707137326611572392137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7431609516435482096522849 5573707137326611572392137)
        ·
          refine ⟨4180280352994958679294103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5573707137326611572392137 4180280352994958679294103)
          ·
            refine ⟨6270420529492438018941155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4180280352994958679294103 6270420529492438018941155)
            ·
              refine ⟨9405630794238657028411733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6270420529492438018941155 9405630794238657028411733)
              ·
                refine ⟨27555558967496065512925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 9405630794238657028411733 27555558967496065512925)
                ·
                  rfl

theorem cell23_1448935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 10].length) (baseStart_1448935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1448935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1448935 prefixEnd_1448935 := by exact prefixLift 1448935
  have htrace : WordTrace (prefixWord ++ tailWord_1448935) baseStart_1448935 baseEnd_1448935 := by
    simpa [prefixWord, tailWord_1448935, baseEnd_1448935] using wordTrace_append hprefix tailTrace_1448935
  have hstable : (prefixWord ++ tailWord_1448935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448935).length < 2 ^ (prefixWord ++ tailWord_1448935).sum := by decide
  have hdescent : baseEnd_1448935 < baseStart_1448935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448985 : List Nat := [1, 2, 1, 2, 1, 1, 5, 1, 2, 3, 4]
def baseStart_1448985 : Nat := 118140960795 + 1448985 * 2 ^ 59
def prefixEnd_1448985 : Nat := 4983230072969 + 3 ^ 40 * 1448985 * 2
def baseEnd_1448985 : Nat := 744025766155118573223745

theorem tailTrace_1448985 : CollatzResearch.WordTrace tailWord_1448985 prefixEnd_1448985 744025766155118573223745 := by
  unfold tailWord_1448985
  simp only [CollatzResearch.WordTrace]
  refine ⟨52848824655582286781260409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35232549770388191187506939 52848824655582286781260409)
  ·
    refine ⟨39636618491686715085945307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52848824655582286781260409 39636618491686715085945307)
    ·
      refine ⟨59454927737530072628917961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39636618491686715085945307 59454927737530072628917961)
      ·
        refine ⟨44591195803147554471688471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59454927737530072628917961 44591195803147554471688471)
        ·
          refine ⟨66886793704721331707532707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44591195803147554471688471 66886793704721331707532707)
          ·
            refine ⟨100330190557081997561299061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66886793704721331707532707 100330190557081997561299061)
            ·
              refine ⟨9405955364726437271371787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 100330190557081997561299061 9405955364726437271371787)
              ·
                refine ⟨14108933047089655907057681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9405955364726437271371787 14108933047089655907057681)
                ·
                  refine ⟨10581699785317241930293261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14108933047089655907057681 10581699785317241930293261)
                  ·
                    refine ⟨3968137419493965723859973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10581699785317241930293261 3968137419493965723859973)
                    ·
                      refine ⟨744025766155118573223745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3968137419493965723859973 744025766155118573223745)
                      ·
                        rfl

theorem cell23_1448985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 3, 4].length) (baseStart_1448985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1448985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1448985 prefixEnd_1448985 := by exact prefixLift 1448985
  have htrace : WordTrace (prefixWord ++ tailWord_1448985) baseStart_1448985 baseEnd_1448985 := by
    simpa [prefixWord, tailWord_1448985, baseEnd_1448985] using wordTrace_append hprefix tailTrace_1448985
  have hstable : (prefixWord ++ tailWord_1448985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448985).length < 2 ^ (prefixWord ++ tailWord_1448985).sum := by decide
  have hdescent : baseEnd_1448985 < baseStart_1448985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448995 : List Nat := [1, 1, 1, 4, 3, 2, 1, 1, 1, 8]
def baseStart_1448995 : Nat := 118140960795 + 1448995 * 2 ^ 59
def prefixEnd_1448995 : Nat := 4983230072969 + 3 ^ 40 * 1448995 * 2
def baseEnd_1448995 : Nat := 248010300320554511366233

theorem tailTrace_1448995 : CollatzResearch.WordTrace tailWord_1448995 prefixEnd_1448995 248010300320554511366233 := by
  unfold tailWord_1448995
  simp only [CollatzResearch.WordTrace]
  refine ⟨52849189385546058489124439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35232792923697372326082959 52849189385546058489124439)
  ·
    refine ⟨79273784078319087733686659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52849189385546058489124439 79273784078319087733686659)
    ·
      refine ⟨118910676117478631600529989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79273784078319087733686659 118910676117478631600529989)
      ·
        refine ⟨22295751772027243425099373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118910676117478631600529989 22295751772027243425099373)
        ·
          refine ⟨8360906914510216284412265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22295751772027243425099373 8360906914510216284412265)
          ·
            refine ⟨6270680185882662213309199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8360906914510216284412265 6270680185882662213309199)
            ·
              refine ⟨9406020278823993319963799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6270680185882662213309199 9406020278823993319963799)
              ·
                refine ⟨14109030418235989979945699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9406020278823993319963799 14109030418235989979945699)
                ·
                  refine ⟨21163545627353984969918549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14109030418235989979945699 21163545627353984969918549)
                  ·
                    refine ⟨248010300320554511366233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 21163545627353984969918549 248010300320554511366233)
                    ·
                      rfl

theorem cell23_1448995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 8].length) (baseStart_1448995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1448995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1448995 prefixEnd_1448995 := by exact prefixLift 1448995
  have htrace : WordTrace (prefixWord ++ tailWord_1448995) baseStart_1448995 baseEnd_1448995 := by
    simpa [prefixWord, tailWord_1448995, baseEnd_1448995] using wordTrace_append hprefix tailTrace_1448995
  have hstable : (prefixWord ++ tailWord_1448995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448995).length < 2 ^ (prefixWord ++ tailWord_1448995).sum := by decide
  have hdescent : baseEnd_1448995 < baseStart_1448995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448996 : List Nat := [2, 3, 1, 4, 1, 1, 2, 3, 2, 1, 3]
def baseStart_1448996 : Nat := 118140960795 + 1448996 * 2 ^ 59
def prefixEnd_1448996 : Nat := 4983230072969 + 3 ^ 40 * 1448996 * 2
def baseEnd_1448996 : Nat := 744031414442318030186195

theorem tailTrace_1448996 : CollatzResearch.WordTrace tailWord_1448996 prefixEnd_1448996 744031414442318030186195 := by
  unfold tailWord_1448996
  simp only [CollatzResearch.WordTrace]
  refine ⟨26424612929271217829955421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35232817239028290439940561 26424612929271217829955421)
  ·
    refine ⟨9909229848476706686233283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26424612929271217829955421 9909229848476706686233283)
    ·
      refine ⟨14863844772715060029349925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9909229848476706686233283 14863844772715060029349925)
      ·
        refine ⟨2786970894884073755503111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14863844772715060029349925 2786970894884073755503111)
        ·
          refine ⟨4180456342326110633254667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2786970894884073755503111 4180456342326110633254667)
          ·
            refine ⟨6270684513489165949882001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4180456342326110633254667 6270684513489165949882001)
            ·
              refine ⟨4703013385116874462411501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6270684513489165949882001 4703013385116874462411501)
              ·
                refine ⟨1763630019418827923404313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4703013385116874462411501 1763630019418827923404313)
                ·
                  refine ⟨1322722514564120942553235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1763630019418827923404313 1322722514564120942553235)
                  ·
                    refine ⟨1984083771846181413829853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1322722514564120942553235 1984083771846181413829853)
                    ·
                      refine ⟨744031414442318030186195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1984083771846181413829853 744031414442318030186195)
                      ·
                        rfl

theorem cell23_1448996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_1448996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1448996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1448996 prefixEnd_1448996 := by exact prefixLift 1448996
  have htrace : WordTrace (prefixWord ++ tailWord_1448996) baseStart_1448996 baseEnd_1448996 := by
    simpa [prefixWord, tailWord_1448996, baseEnd_1448996] using wordTrace_append hprefix tailTrace_1448996
  have hstable : (prefixWord ++ tailWord_1448996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448996).length < 2 ^ (prefixWord ++ tailWord_1448996).sum := by decide
  have hdescent : baseEnd_1448996 < baseStart_1448996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449006 : List Nat := [4, 1, 3, 1, 1, 1, 2, 4, 1, 3, 2]
def baseStart_1449006 : Nat := 118140960795 + 1449006 * 2 ^ 59
def prefixEnd_1449006 : Nat := 4983230072969 + 3 ^ 40 * 1449006 * 2
def baseEnd_1449006 : Nat := 744036549248862991061149

theorem tailTrace_1449006 : CollatzResearch.WordTrace tailWord_1449006 prefixEnd_1449006 744036549248862991061149 := by
  unfold tailWord_1449006
  simp only [CollatzResearch.WordTrace]
  refine ⟨6606198823563275920971859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35233060392337471578516581 6606198823563275920971859)
  ·
    refine ⟨9909298235344913881457789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6606198823563275920971859 9909298235344913881457789)
    ·
      refine ⟨3715986838254342705546671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9909298235344913881457789 3715986838254342705546671)
      ·
        refine ⟨5573980257381514058320007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3715986838254342705546671 5573980257381514058320007)
        ·
          refine ⟨8360970386072271087480011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5573980257381514058320007 8360970386072271087480011)
          ·
            refine ⟨12541455579108406631220017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8360970386072271087480011 12541455579108406631220017)
            ·
              refine ⟨9406091684331304973415013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12541455579108406631220017 9406091684331304973415013)
              ·
                refine ⟨1763642190812119682515315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9406091684331304973415013 1763642190812119682515315)
                ·
                  refine ⟨2645463286218179523772973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1763642190812119682515315 2645463286218179523772973)
                  ·
                    refine ⟨992048732331817321414865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2645463286218179523772973 992048732331817321414865)
                    ·
                      refine ⟨744036549248862991061149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 992048732331817321414865 744036549248862991061149)
                      ·
                        rfl

theorem cell23_1449006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 4, 1, 3, 2].length) (baseStart_1449006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1449006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1449006 prefixEnd_1449006 := by exact prefixLift 1449006
  have htrace : WordTrace (prefixWord ++ tailWord_1449006) baseStart_1449006 baseEnd_1449006 := by
    simpa [prefixWord, tailWord_1449006, baseEnd_1449006] using wordTrace_append hprefix tailTrace_1449006
  have hstable : (prefixWord ++ tailWord_1449006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449006).length < 2 ^ (prefixWord ++ tailWord_1449006).sum := by decide
  have hdescent : baseEnd_1449006 < baseStart_1449006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449015 : List Nat := [1, 1, 3, 1, 2, 2, 1, 1, 3, 4, 4]
def baseStart_1449015 : Nat := 118140960795 + 1449015 * 2 ^ 59
def prefixEnd_1449015 : Nat := 4983230072969 + 3 ^ 40 * 1449015 * 2
def baseEnd_1449015 : Nat := 744041170574753455848607

theorem tailTrace_1449015 : CollatzResearch.WordTrace tailWord_1449015 prefixEnd_1449015 744041170574753455848607 := by
  unfold tailWord_1449015
  simp only [CollatzResearch.WordTrace]
  refine ⟨52849918845473601904852499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35233279230315734603234999 52849918845473601904852499)
  ·
    refine ⟨79274878268210402857278749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52849918845473601904852499 79274878268210402857278749)
    ·
      refine ⟨29728079350578901071479531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79274878268210402857278749 29728079350578901071479531)
      ·
        refine ⟨44592119025868351607219297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29728079350578901071479531 44592119025868351607219297)
        ·
          refine ⟨33444089269401263705414473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44592119025868351607219297 33444089269401263705414473)
          ·
            refine ⟨25083066952050947779060855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33444089269401263705414473 25083066952050947779060855)
            ·
              refine ⟨37624600428076421668591283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25083066952050947779060855 37624600428076421668591283)
              ·
                refine ⟨56436900642114632502886925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37624600428076421668591283 56436900642114632502886925)
                ·
                  refine ⟨21163837740792987188582597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56436900642114632502886925 21163837740792987188582597)
                  ·
                    refine ⟨3968219576398685097859237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21163837740792987188582597 3968219576398685097859237)
                    ·
                      refine ⟨744041170574753455848607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3968219576398685097859237 744041170574753455848607)
                      ·
                        rfl

theorem cell23_1449015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 4, 4].length) (baseStart_1449015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1449015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1449015 prefixEnd_1449015 := by exact prefixLift 1449015
  have htrace : WordTrace (prefixWord ++ tailWord_1449015) baseStart_1449015 baseEnd_1449015 := by
    simpa [prefixWord, tailWord_1449015, baseEnd_1449015] using wordTrace_append hprefix tailTrace_1449015
  have hstable : (prefixWord ++ tailWord_1449015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449015).length < 2 ^ (prefixWord ++ tailWord_1449015).sum := by decide
  have hdescent : baseEnd_1449015 < baseStart_1449015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449030 : List Nat := [6, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3]
def baseStart_1449030 : Nat := 118140960795 + 1449030 * 2 ^ 59
def prefixEnd_1449030 : Nat := 4983230072969 + 3 ^ 40 * 1449030 * 2
def baseEnd_1449030 : Nat := 744048872784570897161039

theorem tailTrace_1449030 : CollatzResearch.WordTrace tailWord_1449030 prefixEnd_1449030 744048872784570897161039 := by
  unfold tailWord_1449030
  simp only [CollatzResearch.WordTrace]
  refine ⟨1651577060638101858332767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 35233643960279506311099029 1651577060638101858332767)
  ·
    refine ⟨2477365590957152787499151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1651577060638101858332767 2477365590957152787499151)
    ·
      refine ⟨3716048386435729181248727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2477365590957152787499151 3716048386435729181248727)
      ·
        refine ⟨5574072579653593771873091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3716048386435729181248727 5574072579653593771873091)
        ·
          refine ⟨8361108869480390657809637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5574072579653593771873091 8361108869480390657809637)
          ·
            refine ⟨1567707913027573248339307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8361108869480390657809637 1567707913027573248339307)
            ·
              refine ⟨2351561869541359872508961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1567707913027573248339307 2351561869541359872508961)
              ·
                refine ⟨1763671402156019904381721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2351561869541359872508961 1763671402156019904381721)
                ·
                  refine ⟨1322753551617014928286291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1763671402156019904381721 1322753551617014928286291)
                  ·
                    refine ⟨1984130327425522392429437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1322753551617014928286291 1984130327425522392429437)
                    ·
                      refine ⟨744048872784570897161039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1984130327425522392429437 744048872784570897161039)
                      ·
                        rfl

theorem cell23_1449030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_1449030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1449030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1449030 prefixEnd_1449030 := by exact prefixLift 1449030
  have htrace : WordTrace (prefixWord ++ tailWord_1449030) baseStart_1449030 baseEnd_1449030 := by
    simpa [prefixWord, tailWord_1449030, baseEnd_1449030] using wordTrace_append hprefix tailTrace_1449030
  have hstable : (prefixWord ++ tailWord_1449030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449030).length < 2 ^ (prefixWord ++ tailWord_1449030).sum := by decide
  have hdescent : baseEnd_1449030 < baseStart_1449030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449042 : List Nat := [3, 2, 2, 1, 3, 1, 1, 3, 7]
def baseStart_1449042 : Nat := 118140960795 + 1449042 * 2 ^ 59
def prefixEnd_1449042 : Nat := 4983230072969 + 3 ^ 40 * 1449042 * 2
def baseEnd_1449042 : Nat := 82672781616936094467887

theorem tailTrace_1449042 : CollatzResearch.WordTrace tailWord_1449042 prefixEnd_1449042 82672781616936094467887 := by
  unfold tailWord_1449042
  simp only [CollatzResearch.WordTrace]
  refine ⟨13212725904093946379021345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35233935744250523677390253 13212725904093946379021345)
  ·
    refine ⟨9909544428070459784266009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13212725904093946379021345 9909544428070459784266009)
    ·
      refine ⟨7432158321052844838199507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9909544428070459784266009 7432158321052844838199507)
      ·
        refine ⟨11148237481579267257299261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7432158321052844838199507 11148237481579267257299261)
        ·
          refine ⟨4180589055592225221487223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11148237481579267257299261 4180589055592225221487223)
          ·
            refine ⟨6270883583388337832230835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4180589055592225221487223 6270883583388337832230835)
            ·
              refine ⟨9406325375082506748346253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6270883583388337832230835 9406325375082506748346253)
              ·
                refine ⟨3527372015655940030629845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9406325375082506748346253 3527372015655940030629845)
                ·
                  refine ⟨82672781616936094467887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3527372015655940030629845 82672781616936094467887)
                  ·
                    rfl

theorem cell23_1449042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 3, 7].length) (baseStart_1449042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1449042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1449042 prefixEnd_1449042 := by exact prefixLift 1449042
  have htrace : WordTrace (prefixWord ++ tailWord_1449042) baseStart_1449042 baseEnd_1449042 := by
    simpa [prefixWord, tailWord_1449042, baseEnd_1449042] using wordTrace_append hprefix tailTrace_1449042
  have hstable : (prefixWord ++ tailWord_1449042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449042).length < 2 ^ (prefixWord ++ tailWord_1449042).sum := by decide
  have hdescent : baseEnd_1449042 < baseStart_1449042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449055 : List Nat := [1, 1, 2, 3, 1, 1, 3, 1, 3, 7]
def baseStart_1449055 : Nat := 118140960795 + 1449055 * 2 ^ 59
def prefixEnd_1449055 : Nat := 4983230072969 + 3 ^ 40 * 1449055 * 2
def baseEnd_1449055 : Nat := 248020569933644433116141

theorem tailTrace_1449055 : CollatzResearch.WordTrace tailWord_1449055 prefixEnd_1449055 248020569933644433116141 := by
  unfold tailWord_1449055
  simp only [CollatzResearch.WordTrace]
  refine ⟨52851377765328688736308619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35234251843552459157539079 52851377765328688736308619)
  ·
    refine ⟨79277066647993033104462929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52851377765328688736308619 79277066647993033104462929)
    ·
      refine ⟨59457799985994774828347197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79277066647993033104462929 59457799985994774828347197)
      ·
        refine ⟨22296674994748040560630199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59457799985994774828347197 22296674994748040560630199)
        ·
          refine ⟨33445012492122060840945299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22296674994748040560630199 33445012492122060840945299)
          ·
            refine ⟨50167518738183091261417949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33445012492122060840945299 50167518738183091261417949)
            ·
              refine ⟨18812819526818659223031731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50167518738183091261417949 18812819526818659223031731)
              ·
                refine ⟨28219229290227988834547597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18812819526818659223031731 28219229290227988834547597)
                ·
                  refine ⟨10582210983835495812955349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28219229290227988834547597 10582210983835495812955349)
                  ·
                    refine ⟨248020569933644433116141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10582210983835495812955349 248020569933644433116141)
                    ·
                      rfl

theorem cell23_1449055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 7].length) (baseStart_1449055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1449055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1449055 prefixEnd_1449055 := by exact prefixLift 1449055
  have htrace : WordTrace (prefixWord ++ tailWord_1449055) baseStart_1449055 baseEnd_1449055 := by
    simpa [prefixWord, tailWord_1449055, baseEnd_1449055] using wordTrace_append hprefix tailTrace_1449055
  have hstable : (prefixWord ++ tailWord_1449055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449055).length < 2 ^ (prefixWord ++ tailWord_1449055).sum := by decide
  have hdescent : baseEnd_1449055 < baseStart_1449055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449072 : List Nat := [2, 1, 1, 1, 5, 1, 2, 3, 2, 5]
def baseStart_1449072 : Nat := 118140960795 + 1449072 * 2 ^ 59
def prefixEnd_1449072 : Nat := 4983230072969 + 3 ^ 40 * 1449072 * 2
def baseEnd_1449072 : Nat := 248023479657353244278615

theorem tailTrace_1449072 : CollatzResearch.WordTrace tailWord_1449072 prefixEnd_1449072 248023479657353244278615 := by
  unfold tailWord_1449072
  simp only [CollatzResearch.WordTrace]
  refine ⟨26425998903133550319838735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35234665204178067093118313 26425998903133550319838735)
  ·
    refine ⟨39638998354700325479758103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26425998903133550319838735 39638998354700325479758103)
    ·
      refine ⟨59458497532050488219637155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39638998354700325479758103 59458497532050488219637155)
      ·
        refine ⟨89187746298075732329455733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59458497532050488219637155 89187746298075732329455733)
        ·
          refine ⟨8361351215444599905886475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 89187746298075732329455733 8361351215444599905886475)
          ·
            refine ⟨12542026823166899858829713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8361351215444599905886475 12542026823166899858829713)
            ·
              refine ⟨9406520117375174894122285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12542026823166899858829713 9406520117375174894122285)
              ·
                refine ⟨3527445044015690585295857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9406520117375174894122285 3527445044015690585295857)
                ·
                  refine ⟨2645583783011767938971893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3527445044015690585295857 2645583783011767938971893)
                  ·
                    refine ⟨248023479657353244278615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2645583783011767938971893 248023479657353244278615)
                    ·
                      rfl

theorem cell23_1449072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 3, 2, 5].length) (baseStart_1449072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1449072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1449072 prefixEnd_1449072 := by exact prefixLift 1449072
  have htrace : WordTrace (prefixWord ++ tailWord_1449072) baseStart_1449072 baseEnd_1449072 := by
    simpa [prefixWord, tailWord_1449072, baseEnd_1449072] using wordTrace_append hprefix tailTrace_1449072
  have hstable : (prefixWord ++ tailWord_1449072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449072).length < 2 ^ (prefixWord ++ tailWord_1449072).sum := by decide
  have hdescent : baseEnd_1449072 < baseStart_1449072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449089 : List Nat := [1, 2, 4, 2, 2, 2, 1, 2, 2, 5]
def baseStart_1449089 : Nat := 118140960795 + 1449089 * 2 ^ 59
def prefixEnd_1449089 : Nat := 4983230072969 + 3 ^ 40 * 1449089 * 2
def baseEnd_1449089 : Nat := 248026389381062055441089

theorem tailTrace_1449089 : CollatzResearch.WordTrace tailWord_1449089 prefixEnd_1449089 248026389381062055441089 := by
  unfold tailWord_1449089
  simp only [CollatzResearch.WordTrace]
  refine ⟨52852617847205512543046321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35235078564803675028697547 52852617847205512543046321)
  ·
    refine ⟨39639463385404134407284741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52852617847205512543046321 39639463385404134407284741)
    ·
      refine ⟨7432399384763275201365889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39639463385404134407284741 7432399384763275201365889)
      ·
        refine ⟨5574299538572456401024417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7432399384763275201365889 5574299538572456401024417)
        ·
          refine ⟨4180724653929342300768313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5574299538572456401024417 4180724653929342300768313)
          ·
            refine ⟨3135543490447006725576235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4180724653929342300768313 3135543490447006725576235)
            ·
              refine ⟨4703315235670510088364353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3135543490447006725576235 4703315235670510088364353)
              ·
                refine ⟨3527486426752882566273265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4703315235670510088364353 3527486426752882566273265)
                ·
                  refine ⟨2645614820064661924704949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3527486426752882566273265 2645614820064661924704949)
                  ·
                    refine ⟨248026389381062055441089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2645614820064661924704949 248026389381062055441089)
                    ·
                      rfl

theorem cell23_1449089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 2, 2, 5].length) (baseStart_1449089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1449089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1449089 prefixEnd_1449089 := by exact prefixLift 1449089
  have htrace : WordTrace (prefixWord ++ tailWord_1449089) baseStart_1449089 baseEnd_1449089 := by
    simpa [prefixWord, tailWord_1449089, baseEnd_1449089] using wordTrace_append hprefix tailTrace_1449089
  have hstable : (prefixWord ++ tailWord_1449089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449089).length < 2 ^ (prefixWord ++ tailWord_1449089).sum := by decide
  have hdescent : baseEnd_1449089 < baseStart_1449089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449115 : List Nat := [1, 1, 1, 1, 1, 1, 2, 3, 12]
def baseStart_1449115 : Nat := 118140960795 + 1449115 * 2 ^ 59
def prefixEnd_1449115 : Nat := 4983230072969 + 3 ^ 40 * 1449115 * 2
def baseEnd_1449115 : Nat := 82676946515578118288683

theorem tailTrace_1449115 : CollatzResearch.WordTrace tailWord_1449115 prefixEnd_1449115 82676946515578118288683 := by
  unfold tailWord_1449115
  simp only [CollatzResearch.WordTrace]
  refine ⟨52853566145111318983492799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35235710763407545988995199 52853566145111318983492799)
  ·
    refine ⟨79280349217666978475239199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52853566145111318983492799 79280349217666978475239199)
    ·
      refine ⟨118920523826500467712858799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79280349217666978475239199 118920523826500467712858799)
      ·
        refine ⟨178380785739750701569288199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118920523826500467712858799 178380785739750701569288199)
        ·
          refine ⟨267571178609626052353932299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178380785739750701569288199 267571178609626052353932299)
          ·
            refine ⟨401356767914439078530898449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267571178609626052353932299 401356767914439078530898449)
            ·
              refine ⟨301017575935829308898173837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 401356767914439078530898449 301017575935829308898173837)
              ·
                refine ⟨112881590975935990836815189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 301017575935829308898173837 112881590975935990836815189)
                ·
                  refine ⟨82676946515578118288683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 112881590975935990836815189 82676946515578118288683)
                  ·
                    rfl

theorem cell23_1449115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 12].length) (baseStart_1449115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1449115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1449115 prefixEnd_1449115 := by exact prefixLift 1449115
  have htrace : WordTrace (prefixWord ++ tailWord_1449115) baseStart_1449115 baseEnd_1449115 := by
    simpa [prefixWord, tailWord_1449115, baseEnd_1449115] using wordTrace_append hprefix tailTrace_1449115
  have hstable : (prefixWord ++ tailWord_1449115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449115).length < 2 ^ (prefixWord ++ tailWord_1449115).sum := by decide
  have hdescent : baseEnd_1449115 < baseStart_1449115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449159 : List Nat := [1, 1, 4, 1, 1, 1, 1, 2, 7, 1, 3]
def baseStart_1449159 : Nat := 118140960795 + 1449159 * 2 ^ 59
def prefixEnd_1449159 : Nat := 4983230072969 + 3 ^ 40 * 1449159 * 2
def baseEnd_1449159 : Nat := 744115111789000892447945

theorem tailTrace_1449159 : CollatzResearch.WordTrace tailWord_1449159 prefixEnd_1449159 744115111789000892447945 := by
  unfold tailWord_1449159
  simp only [CollatzResearch.WordTrace]
  refine ⟨52855170956951914498094531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35236780637967942998729687 52855170956951914498094531)
  ·
    refine ⟨79282756435427871747141797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52855170956951914498094531 79282756435427871747141797)
    ·
      refine ⟨14865516831642725952589087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79282756435427871747141797 14865516831642725952589087)
      ·
        refine ⟨22298275247464088928883631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14865516831642725952589087 22298275247464088928883631)
        ·
          refine ⟨33447412871196133393325447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22298275247464088928883631 33447412871196133393325447)
          ·
            refine ⟨50171119306794200089988171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33447412871196133393325447 50171119306794200089988171)
            ·
              refine ⟨75256678960191300134982257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50171119306794200089988171 75256678960191300134982257)
              ·
                refine ⟨56442509220143475101236693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75256678960191300134982257 56442509220143475101236693)
                ·
                  refine ⟨1322871309847112697685235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 56442509220143475101236693 1322871309847112697685235)
                  ·
                    refine ⟨1984306964770669046527853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1322871309847112697685235 1984306964770669046527853)
                    ·
                      refine ⟨744115111789000892447945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1984306964770669046527853 744115111789000892447945)
                      ·
                        rfl

theorem cell23_1449159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 7, 1, 3].length) (baseStart_1449159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1449159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1449159 prefixEnd_1449159 := by exact prefixLift 1449159
  have htrace : WordTrace (prefixWord ++ tailWord_1449159) baseStart_1449159 baseEnd_1449159 := by
    simpa [prefixWord, tailWord_1449159, baseEnd_1449159] using wordTrace_append hprefix tailTrace_1449159
  have hstable : (prefixWord ++ tailWord_1449159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449159).length < 2 ^ (prefixWord ++ tailWord_1449159).sum := by decide
  have hdescent : baseEnd_1449159 < baseStart_1449159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449169 : List Nat := [1, 2, 2, 1, 2, 2, 1, 4, 1, 5, 2]
def baseStart_1449169 : Nat := 118140960795 + 1449169 * 2 ^ 59
def prefixEnd_1449169 : Nat := 4983230072969 + 3 ^ 40 * 1449169 * 2
def baseEnd_1449169 : Nat := 744120246595545853322899

theorem tailTrace_1449169 : CollatzResearch.WordTrace tailWord_1449169 prefixEnd_1449169 744120246595545853322899 := by
  unfold tailWord_1449169
  simp only [CollatzResearch.WordTrace]
  refine ⟨52855535686915686205958561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35237023791277124137305707 52855535686915686205958561)
  ·
    refine ⟨39641651765186764654468921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52855535686915686205958561 39641651765186764654468921)
    ·
      refine ⟨29731238823890073490851691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39641651765186764654468921 29731238823890073490851691)
      ·
        refine ⟨44596858235835110236277537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29731238823890073490851691 44596858235835110236277537)
        ·
          refine ⟨33447643676876332677208153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44596858235835110236277537 33447643676876332677208153)
          ·
            refine ⟨25085732757657249507906115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33447643676876332677208153 25085732757657249507906115)
            ·
              refine ⟨37628599136485874261859173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25085732757657249507906115 37628599136485874261859173)
              ·
                refine ⟨7055362338091101424098595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37628599136485874261859173 7055362338091101424098595)
                ·
                  refine ⟨10583043507136652136147893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7055362338091101424098595 10583043507136652136147893)
                  ·
                    refine ⟨992160328794061137763865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10583043507136652136147893 992160328794061137763865)
                    ·
                      refine ⟨744120246595545853322899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 992160328794061137763865 744120246595545853322899)
                      ·
                        rfl

theorem cell23_1449169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 5, 2].length) (baseStart_1449169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1449169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1449169 prefixEnd_1449169 := by exact prefixLift 1449169
  have htrace : WordTrace (prefixWord ++ tailWord_1449169) baseStart_1449169 baseEnd_1449169 := by
    simpa [prefixWord, tailWord_1449169, baseEnd_1449169] using wordTrace_append hprefix tailTrace_1449169
  have hstable : (prefixWord ++ tailWord_1449169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449169).length < 2 ^ (prefixWord ++ tailWord_1449169).sum := by decide
  have hdescent : baseEnd_1449169 < baseStart_1449169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449196 : List Nat := [2, 2, 1, 1, 2, 4, 4, 1, 1, 5]
def baseStart_1449196 : Nat := 118140960795 + 1449196 * 2 ^ 59
def prefixEnd_1449196 : Nat := 4983230072969 + 3 ^ 40 * 1449196 * 2
def baseEnd_1449196 : Nat := 248044703524405749228425

theorem tailTrace_1449196 : CollatzResearch.WordTrace tailWord_1449196 prefixEnd_1449196 248044703524405749228425 := by
  unfold tailWord_1449196
  simp only [CollatzResearch.WordTrace]
  refine ⟨26428260228908934908595721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35237680305211913211460961 26428260228908934908595721)
  ·
    refine ⟨19821195171681701181446791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26428260228908934908595721 19821195171681701181446791)
    ·
      refine ⟨29731792757522551772170187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19821195171681701181446791 29731792757522551772170187)
      ·
        refine ⟨44597689136283827658255281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29731792757522551772170187 44597689136283827658255281)
        ·
          refine ⟨33448266852212870743691461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44597689136283827658255281 33448266852212870743691461)
          ·
            refine ⟨6271550034789913264442149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33448266852212870743691461 6271550034789913264442149)
            ·
              refine ⟨1175915631523108737082903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6271550034789913264442149 1175915631523108737082903)
              ·
                refine ⟨1763873447284663105624355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1175915631523108737082903 1763873447284663105624355)
                ·
                  refine ⟨2645810170926994658436533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1763873447284663105624355 2645810170926994658436533)
                  ·
                    refine ⟨248044703524405749228425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2645810170926994658436533 248044703524405749228425)
                    ·
                      rfl

theorem cell23_1449196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 5].length) (baseStart_1449196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1449196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1449196 prefixEnd_1449196 := by exact prefixLift 1449196
  have htrace : WordTrace (prefixWord ++ tailWord_1449196) baseStart_1449196 baseEnd_1449196 := by
    simpa [prefixWord, tailWord_1449196, baseEnd_1449196] using wordTrace_append hprefix tailTrace_1449196
  have hstable : (prefixWord ++ tailWord_1449196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449196).length < 2 ^ (prefixWord ++ tailWord_1449196).sum := by decide
  have hdescent : baseEnd_1449196 < baseStart_1449196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449209 : List Nat := [1, 2, 1, 3, 1, 1, 5, 1, 4, 4]
def baseStart_1449209 : Nat := 118140960795 + 1449209 * 2 ^ 59
def prefixEnd_1449209 : Nat := 4983230072969 + 3 ^ 40 * 1449209 * 2
def baseEnd_1449209 : Nat := 248046928607241898940905

theorem tailTrace_1449209 : CollatzResearch.WordTrace tailWord_1449209 prefixEnd_1449209 248046928607241898940905 := by
  unfold tailWord_1449209
  simp only [CollatzResearch.WordTrace]
  refine ⟨52856994606770773037414681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35237996404513848691609787 52856994606770773037414681)
  ·
    refine ⟨39642745955078079778061011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52856994606770773037414681 39642745955078079778061011)
    ·
      refine ⟨59464118932617119667091517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39642745955078079778061011 59464118932617119667091517)
      ·
        refine ⟨22299044599731419875159319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59464118932617119667091517 22299044599731419875159319)
        ·
          refine ⟨33448566899597129812738979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22299044599731419875159319 33448566899597129812738979)
          ·
            refine ⟨50172850349395694719108469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33448566899597129812738979 50172850349395694719108469)
            ·
              refine ⟨4703704720255846379916419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50172850349395694719108469 4703704720255846379916419)
              ·
                refine ⟨7055557080383769569874629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4703704720255846379916419 7055557080383769569874629)
                ·
                  refine ⟨1322916952571956794351493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7055557080383769569874629 1322916952571956794351493)
                  ·
                    refine ⟨248046928607241898940905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1322916952571956794351493 248046928607241898940905)
                    ·
                      rfl

theorem cell23_1449209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 4, 4].length) (baseStart_1449209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1449209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1449209 prefixEnd_1449209 := by exact prefixLift 1449209
  have htrace : WordTrace (prefixWord ++ tailWord_1449209) baseStart_1449209 baseEnd_1449209 := by
    simpa [prefixWord, tailWord_1449209, baseEnd_1449209] using wordTrace_append hprefix tailTrace_1449209
  have hstable : (prefixWord ++ tailWord_1449209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449209).length < 2 ^ (prefixWord ++ tailWord_1449209).sum := by decide
  have hdescent : baseEnd_1449209 < baseStart_1449209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449219 : List Nat := [1, 1, 1, 3, 2, 5, 1, 2, 1, 1, 5]
def baseStart_1449219 : Nat := 118140960795 + 1449219 * 2 ^ 59
def prefixEnd_1449219 : Nat := 4983230072969 + 3 ^ 40 * 1449219 * 2
def baseEnd_1449219 : Nat := 744145920628270657697669

theorem tailTrace_1449219 : CollatzResearch.WordTrace tailWord_1449219 prefixEnd_1449219 744145920628270657697669 := by
  unfold tailWord_1449219
  simp only [CollatzResearch.WordTrace]
  refine ⟨52857359336734544745278711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35238239557823029830185807 52857359336734544745278711)
  ·
    refine ⟨79286039005101817117918067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52857359336734544745278711 79286039005101817117918067)
    ·
      refine ⟨118929058507652725676877101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79286039005101817117918067 118929058507652725676877101)
      ·
        refine ⟨44598396940369772128828913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118929058507652725676877101 44598396940369772128828913)
        ·
          refine ⟨33448797705277329096621685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44598396940369772128828913 33448797705277329096621685)
          ·
            refine ⟨3135824784869749602808283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33448797705277329096621685 3135824784869749602808283)
            ·
              refine ⟨4703737177304624404212425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3135824784869749602808283 4703737177304624404212425)
              ·
                refine ⟨3527802882978468303159319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4703737177304624404212425 3527802882978468303159319)
                ·
                  refine ⟨5291704324467702454738979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3527802882978468303159319 5291704324467702454738979)
                  ·
                    refine ⟨7937556486701553682108469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5291704324467702454738979 7937556486701553682108469)
                    ·
                      refine ⟨744145920628270657697669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7937556486701553682108469 744145920628270657697669)
                      ·
                        rfl

theorem cell23_1449219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 2, 1, 1, 5].length) (baseStart_1449219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1449219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1449219 prefixEnd_1449219 := by exact prefixLift 1449219
  have htrace : WordTrace (prefixWord ++ tailWord_1449219) baseStart_1449219 baseEnd_1449219 := by
    simpa [prefixWord, tailWord_1449219, baseEnd_1449219] using wordTrace_append hprefix tailTrace_1449219
  have hstable : (prefixWord ++ tailWord_1449219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449219).length < 2 ^ (prefixWord ++ tailWord_1449219).sum := by decide
  have hdescent : baseEnd_1449219 < baseStart_1449219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449249 : List Nat := [1, 2, 3, 2, 1, 1, 1, 3, 3, 3, 3]
def baseStart_1449249 : Nat := 118140960795 + 1449249 * 2 ^ 59
def prefixEnd_1449249 : Nat := 4983230072969 + 3 ^ 40 * 1449249 * 2
def baseEnd_1449249 : Nat := 744161325047905540322531

theorem tailTrace_1449249 : CollatzResearch.WordTrace tailWord_1449249 prefixEnd_1449249 744161325047905540322531 := by
  unfold tailWord_1449249
  simp only [CollatzResearch.WordTrace]
  refine ⟨52858453526625859868870801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35238969017750573245913867 52858453526625859868870801)
  ·
    refine ⟨39643840144969394901653101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52858453526625859868870801 39643840144969394901653101)
    ·
      refine ⟨14866440054363523088119913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39643840144969394901653101 14866440054363523088119913)
      ·
        refine ⟨11149830040772642316089935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14866440054363523088119913 11149830040772642316089935)
        ·
          refine ⟨16724745061158963474134903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11149830040772642316089935 16724745061158963474134903)
          ·
            refine ⟨25087117591738445211202355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16724745061158963474134903 25087117591738445211202355)
            ·
              refine ⟨37630676387607667816803533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25087117591738445211202355 37630676387607667816803533)
              ·
                refine ⟨14111503645352875431301325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37630676387607667816803533 14111503645352875431301325)
                ·
                  refine ⟨5291813867007328286737997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14111503645352875431301325 5291813867007328286737997)
                  ·
                    refine ⟨1984430200127748107526749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5291813867007328286737997 1984430200127748107526749)
                    ·
                      refine ⟨744161325047905540322531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1984430200127748107526749 744161325047905540322531)
                      ·
                        rfl

theorem cell23_1449249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 3, 3, 3].length) (baseStart_1449249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1449249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1449249 prefixEnd_1449249 := by exact prefixLift 1449249
  have htrace : WordTrace (prefixWord ++ tailWord_1449249) baseStart_1449249 baseEnd_1449249 := by
    simpa [prefixWord, tailWord_1449249, baseEnd_1449249] using wordTrace_append hprefix tailTrace_1449249
  have hstable : (prefixWord ++ tailWord_1449249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449249).length < 2 ^ (prefixWord ++ tailWord_1449249).sum := by decide
  have hdescent : baseEnd_1449249 < baseStart_1449249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449267 : List Nat := [1, 1, 1, 2, 5, 3, 3, 2, 1, 2, 2]
def baseStart_1449267 : Nat := 118140960795 + 1449267 * 2 ^ 59
def prefixEnd_1449267 : Nat := 4983230072969 + 3 ^ 40 * 1449267 * 2
def baseEnd_1449267 : Nat := 744170567699686469897449

theorem tailTrace_1449267 : CollatzResearch.WordTrace tailWord_1449267 prefixEnd_1449267 744170567699686469897449 := by
  unfold tailWord_1449267
  simp only [CollatzResearch.WordTrace]
  refine ⟨52859110040560648943026055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35239406693707099295350703 52859110040560648943026055)
  ·
    refine ⟨79288665060840973414539083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52859110040560648943026055 79288665060840973414539083)
    ·
      refine ⟨118932997591261460121808625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79288665060840973414539083 118932997591261460121808625)
      ·
        refine ⟨89199748193446095091356469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118932997591261460121808625 89199748193446095091356469)
        ·
          refine ⟨8362476393135571414814669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 89199748193446095091356469 8362476393135571414814669)
          ·
            refine ⟨3135928647425839280555501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8362476393135571414814669 3135928647425839280555501)
            ·
              refine ⟨1175973242784689730208313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3135928647425839280555501 1175973242784689730208313)
              ·
                refine ⟨881979932088517297656235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1175973242784689730208313 881979932088517297656235)
                ·
                  refine ⟨1322969898132775946484353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 881979932088517297656235 1322969898132775946484353)
                  ·
                    refine ⟨992227423599581959863265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1322969898132775946484353 992227423599581959863265)
                    ·
                      refine ⟨744170567699686469897449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 992227423599581959863265 744170567699686469897449)
                      ·
                        rfl

theorem cell23_1449267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 3, 2, 1, 2, 2].length) (baseStart_1449267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1449267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1449267 prefixEnd_1449267 := by exact prefixLift 1449267
  have htrace : WordTrace (prefixWord ++ tailWord_1449267) baseStart_1449267 baseEnd_1449267 := by
    simpa [prefixWord, tailWord_1449267, baseEnd_1449267] using wordTrace_append hprefix tailTrace_1449267
  have hstable : (prefixWord ++ tailWord_1449267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449267).length < 2 ^ (prefixWord ++ tailWord_1449267).sum := by decide
  have hdescent : baseEnd_1449267 < baseStart_1449267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449277 : List Nat := [1, 4, 1, 5, 1, 2, 2, 1, 2, 4]
def baseStart_1449277 : Nat := 118140960795 + 1449277 * 2 ^ 59
def prefixEnd_1449277 : Nat := 4983230072969 + 3 ^ 40 * 1449277 * 2
def baseEnd_1449277 : Nat := 248058567502077143590801

theorem tailTrace_1449277 : CollatzResearch.WordTrace tailWord_1449277 prefixEnd_1449277 248058567502077143590801 := by
  unfold tailWord_1449277
  simp only [CollatzResearch.WordTrace]
  refine ⟨52859474770524420650890085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35239649847016280433926723 52859474770524420650890085)
  ·
    refine ⟨9911151519473328872041891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52859474770524420650890085 9911151519473328872041891)
    ·
      refine ⟨14866727279209993308062837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9911151519473328872041891 14866727279209993308062837)
      ·
        refine ⟨1393755682425936872630891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14866727279209993308062837 1393755682425936872630891)
        ·
          refine ⟨2090633523638905308946337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1393755682425936872630891 2090633523638905308946337)
          ·
            refine ⟨1567975142729178981709753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2090633523638905308946337 1567975142729178981709753)
            ·
              refine ⟨1175981357046884236282315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1567975142729178981709753 1175981357046884236282315)
              ·
                refine ⟨1763972035570326354423473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1175981357046884236282315 1763972035570326354423473)
                ·
                  refine ⟨1322979026677744765817605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1763972035570326354423473 1322979026677744765817605)
                  ·
                    refine ⟨248058567502077143590801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1322979026677744765817605 248058567502077143590801)
                    ·
                      rfl

theorem cell23_1449277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 2, 1, 2, 4].length) (baseStart_1449277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1449277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1449277 prefixEnd_1449277 := by exact prefixLift 1449277
  have htrace : WordTrace (prefixWord ++ tailWord_1449277) baseStart_1449277 baseEnd_1449277 := by
    simpa [prefixWord, tailWord_1449277, baseEnd_1449277] using wordTrace_append hprefix tailTrace_1449277
  have hstable : (prefixWord ++ tailWord_1449277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449277).length < 2 ^ (prefixWord ++ tailWord_1449277).sum := by decide
  have hdescent : baseEnd_1449277 < baseStart_1449277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
